{-# LANGUAGE LambdaCase, TupleSections #-}
module Ra (
  bind_to_table,
  pat_match,
  reduce_deep
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

import Data.Tuple.Extra ( second, (***) )
import Data.Function ( (&) )
import Data.Maybe ( maybeToList, isNothing )
import Data.Coerce ( coerce )
import Control.Applicative ( (<|>) )
import Control.Exception ( assert )

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
  -> SymTable
pat_multi_match expand branch expr pats =
  let values = reduce_deep branch expr []
  in union_sym_tables $ values & map (\(Sym (parts, expr')) ->
    case expand expr' of
      Just args | let arg_matches :: [SymTable]
                      arg_matches = map (uncurry (pat_match branch . mksym)) (zip args pats)
                , and $ map (\(SymTable t) -> not $ M.null t) arg_matches
                -> union_sym_tables arg_matches -- should be disjoint bindings because the args contribute different variables
      Nothing -> SymTable empty
  )

-- invoke as: `unions . concatMap (map ((unions . concatMap . pat_match table) . unLoc) . zip args . m_pats) mg_alts` on `MatchGroup`'s `mg_alts`
pat_match ::
  StackBranch
  -> Sym
  -> Pat Id
  -> SymTable -- the new bindings in _this stack frame only_, even if new ones are resolved above and below
-- all new matches from the pat match; empty denotes the match failed (we'll bind wildcards under `_` which will be ignored later since it's an illegal variable and function name)
-- Valid HsExpr: HsApp, OpApp, NegApp, ExplicitTuple, ExplicitList, (SectionL, SectionR) (for data types that are named by operators, e.g. `:`; I might not support this in v1 because it's so thin)
-- Valid Pat:
pat_match branch sym@(Sym (m_parts, expr)) = \case
  -- empty
  WildPat ty ->
    let fake_name = mkSystemName (mkVarOccUnique $ mkFastString "_") (mkVarOcc "_")
        fake_var = mkLocalVar VanillaId fake_name ty vanillaIdInfo
    in SymTable $ singleton fake_var [Sym (Nothing, expr)]
  -- wrapper
  LazyPat (L _ pat) -> pat_match branch sym pat
  ParPat (L _ pat) -> pat_match branch sym pat
  BangPat (L _ pat) -> pat_match branch sym pat
  SigPatOut (L _ pat) _ -> pat_match branch sym pat
  -- base
  VarPat (L _ v) -> SymTable $ singleton v [Sym (Nothing, expr)]
  -- container
  ListPat pats _ _ -> union_sym_tables $ map (pat_match branch sym . unLoc) pats -- encodes the logic that all elements of a list might be part of the pattern regardless of order
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
      let matcher x | let (con, args) = deapp x -- x is in NF thanks to pat_multi_match; this assumes it
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

reduce_deep :: StackBranch -> Sym -> [[Sym]] -> [Sym]
-- TODO this error bank is getting pretty ugly on account of Sym and the repeated arguments of application. Consider refactor.
reduce_deep _ (Sym (_, HsConLikeOut _)) (_:_) = error "Only bare ConLike should make it to `reduce_deep`"
reduce_deep _ (Sym (_, HsOverLit _)) (_:_) = error "Application on OverLit"
reduce_deep _ (Sym (_, HsLit _)) (_:_) = error "Application on Lit"
reduce_deep _ (Sym (_, ExplicitTuple _ _)) (_:_) = error "Application on ExplicitTuple"

reduce_deep branch sym@(Sym (m_parts, expr)) args =
  let terminal = assert (isNothing m_parts) [sym]
      unwrap1 v = reduce_deep branch (Sym (m_parts, v)) args
      unwrap :: [HsExpr Id] -> [Sym]
      unwrap = concatMap (flip (reduce_deep branch) args . Sym . (m_parts,))
      -- . uncurry zip . ( -- over all new expressions from reduce1
      --     repeat . (flip update_head branch) . second . (union_sym_tables.) . flip (:) . pure -- make many copies of the branch unioned with the new binds from reduce1
      --     *** id -- BOOKMARK: fix this error
      --   ) -- what happens when reduce1 is identity? Then it's thrown into reduce_deep again which matches against this. It's a similar story with `iterate`, but I think when it converges to a fixed point, somehow it stops?
        -- no, we need to be explicit because GHC isn't going to detect all cycles, even if we're applying a function over and over again to the same argument.
        -- not true, GHC can detect the cycle when the thunk is reforced. I need it to be the same thunk. The problem is that `reduce_deep` and `reduce1` interact.
  in case expr of
    HsLamCase mg -> reduce_deep branch (mksym $ HsLam mg) args
    
    HsLam mg | let loc = getLoc $ mg_alts mg
             , not $ loc `elem` map fst branch -> -- beware about `noLoc`s showing up here: maybe instead break out the pattern matching code
      let pat_matches :: SymTable
          pat_matches =
            union_sym_tables $ (unLoc $ mg_alts mg) & concatMap ( -- over function body alternatives
              map ( -- over arguments
                union_sym_tables . map ( -- over possible expressions
                  uncurry (pat_match branch) -- share the same branch
                ) . (uncurry zip) . (id *** repeat)
              ) . zip args . map unLoc . m_pats . unLoc -- `args` FINALLY USED HERE
            )
          next_arg_binds = union_sym_tables (pat_matches : (maybeToList m_parts))
      in if matchGroupArity mg < length args
        then [Sym (Just next_arg_binds, HsLam (mg_drop (length args) mg))] -- partial
        else
          let next_explicit_binds = grhs_binds mg
              next_exprs = grhs_exprs mg
              next_frame = (loc, union_sym_tables [next_explicit_binds, next_arg_binds])
              next_branch = next_frame : branch
              next_args = map (drop (length args - matchGroupArity mg)) args
          in concatMap (flip (reduce_deep next_branch) next_args . mksym) next_exprs
          
    HsVar (L _ v) | Just left_exprs <- branch_lookup v branch ->
      let flatten :: [(StackBranch, [a])] -> (StackBranch, [a])
          flatten = foldr (\(a, b) (a', b') -> (union_branches [a, a'], b ++ b')) ([], []) -- sometimes pointfree isn't worth it
          -- flatten = foldr (uncurry (***) . (((union_branches.) . flip (:) . pure) *** (++))) ([], []) -- not going to lie, the point-free here is a bit ridiculous
          nf_left = concatMap (flip (reduce_deep branch) args) left_exprs -- TODO The whole StackBranch structure is a little screwy, because all of them should eventually lead to lambdas except for unresolvable bindings. Therefore, 
      in foldr ((++) . flip (reduce_deep branch) args) [] nf_left
      
    HsApp _ _ ->
      let (fun, next_args) = deapp expr
      in reduce_deep branch (mksym fun) (map (pure . mksym) next_args ++ args)
      
    OpApp (L _ l) (L _ op) _ (L _ r) -> reduce_deep branch (mksym op) ([mksym l]:[mksym r]:args)
    
    -- Wrappings
    
    NegApp (L _ v) _ -> unwrap1 v
    HsPar (L _ v) -> unwrap1 v
    SectionL (L _ v) (L _ op) -> reduce_deep branch (Sym (m_parts, op)) ([Sym (m_parts, v)] : args)
    SectionR (L _ (HsVar (L _ op))) (L _ v) | Just branch_exprs<- branch_lookup op branch -> branch_exprs & foldr (\(Sym (m_table, HsLam mg)) -> (++(reduce_deep branch (Sym (m_table, HsLam (mg_flip mg))) ([Sym (m_parts, v)] : args)))) [] -- BOOMARK: also do the operator constructor case
    -- Take the mapping from the function, reduce_deep'd to HsLam, then pat-match against all arguments
    -- Or, rearrange to an application of `flip` on the app, then the section. This feels way nicer, but the user is just not allowed to rename `flip`, which is unreasonable.
    HsCase (L _ x) mg -> reduce_deep branch (Sym (m_parts, HsApp (noLoc $ HsLam mg) (noLoc x))) args -- refactor as HsLam so we can just use that pat match code
    HsIf _ (L _ if_) (L _ then_) (L _ else_) -> unwrap [then_, else_]
    HsMultiIf ty rhss ->
      let next_explicit_binds = grhs_binds rhss
          next_exprs = grhs_exprs rhss
      in concatMap (flip (reduce_deep branch) args . Sym . (Just $ union_sym_tables (next_explicit_binds : maybeToList m_parts),)) next_exprs
      -- (HsLam (MatchGroup {
      --   mg_alts = noLoc $ map (noLoc Match {
      --       m_ctxt = error "Accessed m_ctxt of contrived Match",
      --       m_pats = [],
      --       m_grhss = GRHSs {
      --           grhssGRHSs = rhss,
      --           grhssLocalBinds = noLoc $ EmptyLocalBinds
      --         }
      --     }) rhss,
      --   mg_arg_tys = [],
      --   mg_res_ty = ty,
      --   mg_origin = Generated
      -- }))) -- also refactor so we can just use that pat match code
    HsLet _ (L _ expr) -> unwrap1 expr -- assume local bindings already caught by surrounding function body (HsLam case)
    -- Terminal forms
  
    HsConLikeOut _ -> terminal
    HsOverLit _ -> terminal
    HsLit _ -> terminal
    ExplicitTuple _ _ -> terminal
    ExplicitSum _ _ _ _ -> terminal
    ExplicitList _ _ _ -> terminal
    ExplicitPArr _ _ -> terminal
  
-- 
-- reduce1 :: StackBranch -> Sym -> Maybe (SymTable, [Sym]) -- only return new and updated entries, stop at names and literals... except I guess at a direct application? That dictates whether or not this is the thing that should update the stack table, or if it should just return a flat symbol table. 
-- reduce1 branch (Sym (_, expr)) = case expr of
  
  
  -- ignore HsVar and HsApp, which should be fulfilled by the calling scope
  -- Note that the table isn't always updated, so we can't rely on it. Instead, we must wrap in Maybe
  -- 