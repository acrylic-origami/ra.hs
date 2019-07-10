{-# LANGUAGE LambdaCase, TupleSections #-}
module Ra (
  bind_to_table,
  pat_match,
  reduce_deep,
  reduce1
) where

import GHC
import DataCon ( dataConName )
import Name ( mkSystemName )
import OccName ( mkVarOcc )
import Unique ( mkVarOccUnique )
import ConLike ( ConLike (..) )
import FastString ( mkFastString ) -- for WildPat synthesis
import Var ( mkLocalVar, varName ) -- for WildPat synthesis
import IdInfo ( vanillaIdInfo, IdDetails(VanillaId) ) -- for WildPat synthesis

import Control.Applicative ( (<|>) )
import Data.Tuple.Extra ( second, (***) )
import Data.Function ( (&) )
import Data.Maybe ( maybeToList )
import Data.Coerce ( coerce )

import Data.Map.Strict ( unionsWith, unions, unionWith, union, singleton, empty, (!?) )
import qualified Data.Map.Strict as M ( null )
-- import qualified Data.Set as S ( insert )

import qualified Ra.Refs as Refs
import {-# SOURCE #-} Ra.GHC
import Ra.Stack
import Ra.Extra

-- type NFStackTable = Map Id NF
-- data NF = WHNF (HsExpr Id) | Ref (HsExpr Id)
-- WHNF is either a literal, data construction, or unknown function app;
-- Ref holds the expression that spits out the pipe that holds the value[s] that we must trace in a separate traversal over ref types. Note the Located because we use SrcSpan to find specific write instances

deapp :: HsExpr Id -> (HsExpr Id, [HsExpr Id])
deapp expr = case expr of
  HsApp l r -> (id *** (++[unLoc r])) (deapp $ unLoc l)
  _ -> (expr, [])

pat_multi_match ::
  (HsExpr Id -> Maybe [HsExpr Id]) -- predicate and expression expander
  -> StackBranch -- full symbol table
  -> Sym
  -> [Pat Id]
  -> StackBranch
pat_multi_match expand branch expr pats =
  let (table', values) = reduce_deep branch expr []
  in union_sym_tables $ values & map (\(Sym (parts, expr)) ->
    case expand expr of
      Just args | let arg_matches :: [SymTable]
                      arg_matches = map (uncurry (pat_match branch . mksym)) (zip args pats)
                , and $ map (\(SymTable t) -> not $ M.null t) arg_matches -> union_sym_tables arg_matches -- should be disjoint bindings because the args contribute different variables
      Nothing -> SymTable empty
  )

-- invoke as: `unions . concatMap (map ((unions . concatMap . pat_match table) . unLoc) . zip args . m_pats) mg_alts` on `MatchGroup`'s `mg_alts`
pat_match ::
  StackBranch
  -> Sym
  -> Pat Id
  -> StackBranch -- the _difference_ in each stack frame
-- all new matches from the pat match; empty denotes the match failed (we'll bind wildcards under `_` which will be ignored later since it's an illegal variable and function name)
-- Valid HsExpr: HsApp, OpApp, NegApp, ExplicitTuple, ExplicitList, (SectionL, SectionR) (for data types that are named by operators, e.g. `:`; I might not support this in v1 because it's so thin)
-- Valid Pat: 
-- empty pats
pat_match branch sym@(Sym (m_parts, expr)) = \case
  -- empty
  WildPat ty ->
    let fake_name = mkSystemName (mkVarOccUnique $ mkFastString "_") (mkVarOcc "_")
        fake_var = mkLocalVar VanillaId fake_name ty vanillaIdInfo
        next_table = SymTable $ singleton fake_var [Sym (Nothing, expr)]
    in update_head_table next_table (clear_branch branch)
  -- wrapper
  LazyPat (L _ pat) -> pat_match branch sym pat
  ParPat (L _ pat) -> pat_match branch sym pat
  BangPat (L _ pat) -> pat_match branch sym pat
  SigPatOut (L _ pat) _ -> pat_match branch sym pat
  -- base
  VarPat (L _ v) -> update_head_table (SymTable singleton v [Sym (Nothing, expr)]) (clear_branch branch)
  -- container
  ListPat pats _ _ -> union_branches $ map (pat_match branch sym . unLoc) pats -- encodes the logic that all elements of a list might be part of the pattern regardless of order -- TODO: is this the right branch? Should it be reduced?
  AsPat (L _ bound) (L _ pat) -> union_sym_tables [
      SymTable $ singleton bound [sym]
      , pat_match branch (mksym expr) pat
    ] -- NB this should also be disjoint (between the binding and the internal pattern); just guard in case
  TuplePat pats _ _ -> pat_multi_match (\case 
      ExplicitTuple args _ -> Just (map ((\(Present (L _ expr')) -> expr') . unLoc) args)
      _ -> Nothing
    ) branch sym (map unLoc pats)
      
  ConPatOut{ pat_con = L _ (RealDataCon pat_con'), pat_args = d_pat_args } -> case d_pat_args of
    PrefixCon pats ->
      let matcher x | let (con, args) = deapp x
                    , HsVar (L _ id) <- con
                    , varName id == dataConName pat_con' = Just args
                    | otherwise = Nothing
      in pat_multi_match matcher branch sym (map unLoc pats)
    
    -- case expr of
    --   HsVar id | varName id == dataConName pat_con -> 
    --   HsApp l r -> 
    --     let fst $ iterate (\(l, args) -> case l of
    --       HsApp l' r' -> (l', (r' : args))
    --       HsCase mg ->  -- need to update the symbol table after pattern matching! Normally, it would be great to have that function that spits back the new symbol table and the tree of expressions. Then it should be a separate function that calls patterns matching. I forget why now I wanted to have it all done within pattern match. We already had the idea for this function. It drills all the way through args.
    --       _ -> )
    --   HsCase -> 
    --   let tied = tie expr
    --   in unions $ map (deapp . bool () (tie (table))) (snd tied)
    RecCon _ -> error "Record syntax yet to be implemented"

reduce_deep :: StackBranch -> Sym -> [[Sym]] -> (StackBranch, [Sym]) -- is this Expr <-> Sym asymmetry okay in the arg/return okay?
-- TODO this error bank is getting pretty ugly on account of Sym and the repeated arguments of application. Consider refactor.
reduce_deep _ (Sym (_, HsConLikeOut _)) (_:_) = error "Only bare ConLike should make it to `reduce_deep`"
reduce_deep _ (Sym (_, HsOverLit _)) (_:_) = error "Application on OverLit"
reduce_deep _ (Sym (_, HsLit _)) (_:_) = error "Application on Lit"
reduce_deep _ (Sym (_, ExplicitTuple _ _)) (_:_) = error "Application on ExplicitTuple"

reduce_deep branch (Sym (m_parts, expr)) nf_args = case expr of
  HsLamCase mg -> reduce_deep branch (mksym $ HsLam mg) nf_args
  
  HsLam mg | let loc = getLoc $ mg_alts mg
           , not $ loc `elem` map fst branch -> 
    let pat_matches :: SymTable
        pat_matches =
          union_branches $ (unLoc $ mg_alts mg) & concatMap ( -- over function body alternatives
            map ( -- over arguments
              union_sym_tables . map ( -- over possible expressions
                uncurry (pat_match undefined) -- TODO which branch?
              ) . (uncurry zip) . (id *** repeat)
            ) . zip nf_args . map unLoc . m_pats . unLoc -- `nf_args` FINALLY USED HERE
          )
        next_arg_binds = union_sym_tables (pat_matches : (maybeToList m_parts))
    in if matchGroupArity mg < length nf_args
      then (undefined, [Sym (Just next_arg_binds, HsLam (mg_drop (length nf_args) mg))]) -- partial -- TODO figure out what branch should go there; is it `branch`?
      else
        let next_explicit_binds = grhs_binds mg
            next_exprs = grhs_exprs mg
            next_frame = (loc, union_sym_tables [next_explicit_binds, next_arg_binds])
            next_branch = next_frame : branch -- TODO figure out what branch should go there
            next_args = map (drop (length nf_args - matchGroupArity mg)) nf_args
        in (union_branches *** concat) $ unzip $ map (flip (reduce_deep next_branch) next_args . mksym) next_exprs -- TODO figure out if branch needs to be advanced here
        
  HsVar (L _ v) | Just left_exprs <- foldr ((<|>) . (!?v) . coerce . snd) Nothing branch ->
    let flatten :: [(StackBranch, [a])] -> (StackBranch, [a])
        flatten = foldr (\(a, b) (a', b') -> (union_branches [a, a'], b ++ b')) ([], []) -- sometimes pointfree isn't worth it
        -- flatten = foldr (uncurry (***) . (((union_branches.) . flip (:) . pure) *** (++))) ([], []) -- not going to lie, the point-free here is a bit ridiculous
        (left_branch, nf_left) = flatten $ map ( -- over all expressions `v` took on
            flatten . map (($nf_args) . uncurry reduce_deep) . uncurry zip . ( -- over all new expressions from reduce1
              repeat . (flip update_head branch {- should this be `branch`? -}) . second . (union_sym_tables.) . flip (:) . pure -- make many copies of the branch unioned with the new binds from reduce1 -- TODO don't quite remember if update_head was on the new entry, or the old one `branch`. Either way, bigger-picture I have to sort all this crap out about returning only a delta
              *** id
            ) . reduce1 branch
          ) left_exprs -- BOOKMARK The whole StackBranch structure is a little screwy, because all of them should eventually lead to lambdas except for unresolvable bindings. Therefore, 
    in foldl (\(branch', nf_exprs) expr -> reduce_deep branch' expr nf_args) (left_branch, []) nf_left
    
  HsApp _ _ ->
    let (fun, args) = deapp expr
    in reduce_deep branch (mksym fun) (map (pure . mksym) args ++ nf_args)
    
  OpApp (L _ l) (L _ op) _ (L _ r) -> reduce_deep branch (mksym op) ([mksym l]:[mksym r]:nf_args)
  
  NegApp (L _ r) _ -> reduce_deep branch (mksym r) nf_args
  
  _ -> (branch, [mksym expr])

-- 
reduce1 :: StackBranch -> Sym -> (SymTable, [Sym]) -- only return new and updated entries, stop at names and literals... except I guess at a direct application? That dictates whether or not this is the thing that should update the stack table, or if it should just return a flat symbol table. 
reduce1 table expr = undefined -- case expr of
  -- ignore HsVar and HsApp, which should be fulfilled by the calling scope
  