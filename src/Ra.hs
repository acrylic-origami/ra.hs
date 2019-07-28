{-# LANGUAGE LambdaCase, TupleSections #-}
module Ra (
  pat_match,
  reduce_deep
) where

import GHC
import DataCon ( dataConName )
import Name ( mkSystemName, nameOccName )
import Var ( varName )
import OccName ( mkVarOcc, occNameString )
import Unique ( mkVarOccUnique )
import ConLike ( ConLike (..) )
import FastString ( mkFastString ) -- for WildPat synthesis
import Var ( mkLocalVar, varName ) -- for WildPat synthesis
import IdInfo ( vanillaIdInfo, IdDetails(VanillaId) ) -- for WildPat synthesis

import Data.Char ( isLower )
import Data.Tuple.Extra ( second, (***), both )
import Data.Function ( (&) )
import Data.Maybe ( maybeToList, isNothing )
import Data.Generics.Extra ( constr_ppr )
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

unHsWrap :: HsExpr Id -> HsExpr Id
unHsWrap expr = case expr of
  HsWrap _ v -> unHsWrap v
  _ -> expr
  

deapp :: HsExpr Id -> (HsExpr Id, [HsExpr Id])
deapp expr =
  let unwrapped = unHsWrap expr in
    case unwrapped of
      HsApp l r -> (id *** (++[unLoc r])) (deapp $ unLoc l)
      _ -> (unwrapped, [])

app :: HsExpr Id -> [HsExpr Id] -> HsExpr Id
app expr = foldl (curry (uncurry HsApp . both noLoc)) expr

pat_multi_match ::
  (HsExpr Id -> Maybe [HsExpr Id]) -- predicate and expression expander
  -> StackBranch -- full symbol table
  -> Sym
  -> [Pat Id]
  -> SymTable
pat_multi_match expand branch expr pats =
  let values = reduce_deep branch expr []
      mapper expr' = case expand expr' of
        Just args | let arg_matches :: [SymTable]
                        arg_matches = map (uncurry (pat_match branch)) (zip args pats)
                  , and $ map (not . M.null) arg_matches
                  -> union_sym_tables arg_matches -- should be disjoint bindings because the args contribute different variables
        Nothing -> empty
  in union_sym_tables $ map mapper values

-- invoke as: `unions . concatMap (map ((unions . concatMap . pat_match table) . unLoc) . zip args . m_pats) mg_alts` on `MatchGroup`'s `mg_alts`
pat_match ::
  StackBranch
  -> Sym
  -> Pat Id
  -> SymTable -- the new bindings in _this stack frame only_, even if new ones are resolved above and below
-- all new matches from the pat match; empty denotes the match failed (we'll bind wildcards under `_` which will be ignored later since it's an illegal variable and function name)
-- Valid HsExpr: HsApp, OpApp, NegApp, ExplicitTuple, ExplicitList, (SectionL, SectionR) (for data types that are named by operators, e.g. `:`; I might not support this in v1 because it's so thin)
-- Valid Pat:
pat_match branch expr pat = case pat of
  -- empty
  WildPat ty ->
    let fake_name = mkSystemName (mkVarOccUnique $ mkFastString "_") (mkVarOcc "_")
        fake_var = mkLocalVar VanillaId fake_name ty vanillaIdInfo
    in singleton fake_var [expr]
  -- wrapper
  LazyPat (L _ pat) -> pat_match branch expr pat
  ParPat (L _ pat) -> pat_match branch expr pat
  BangPat (L _ pat) -> pat_match branch expr pat
  SigPatOut (L _ pat) _ -> pat_match branch expr pat
  -- base
  VarPat (L _ v) -> singleton v [expr]
  LitPat _ -> empty -- no new name bindings
  NPat _ _ _ _ -> empty
  -- container
  ListPat pats _ _ -> union_sym_tables $ map (pat_match branch expr . unLoc) pats -- encodes the logic that all elements of a list might be part of the pattern regardless of order
  AsPat (L _ bound) (L _ pat) -> union_sym_tables [
      singleton bound [expr]
      , pat_match branch expr pat
    ] -- NB this should also be disjoint (between the binding and the internal pattern); just guard in case
  TuplePat pats _ _ -> pat_multi_match (\case 
      ExplicitTuple args _ -> Just (map ((\(Present (L _ expr')) -> expr') . unLoc) args)
      _ -> Nothing
    ) branch expr (map unLoc pats)
      
  ConPatOut{ pat_con = L _ (RealDataCon pat_con'), pat_args = d_pat_args } -> case d_pat_args of
    PrefixCon pats ->
      let matcher x | let (con, args) = deapp x -- x is in NF thanks to pat_multi_match; this assumes it
                    , HsVar (L _ id) <- con
                    , varName id == dataConName pat_con' = Just args
                    | otherwise = Nothing
      in pat_multi_match matcher branch expr (map unLoc pats)
    
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
  _ -> error $ constr_ppr pat

reduce_deep :: StackBranch -> Sym -> [[Sym]] -> [Sym]
-- TODO this error bank is getting pretty ugly on account of Sym and the repeated arguments of application. Consider refactor.
reduce_deep _ (HsConLikeOut _) args@(_:_) = error "Only bare ConLike should make it to `reduce_deep`" -- $ (map constr_ppr args) ++ 
reduce_deep _ (HsOverLit _) (_:_) = error "Application on OverLit"
reduce_deep _ (HsLit _) (_:_) = error "Application on Lit"
reduce_deep _ (ExplicitTuple _ _) (_:_) = error "Application on ExplicitTuple"

reduce_deep branch expr args =
  let terminal =
        -- assert (isNothing m_parts) $
        foldl (\ress args -> [HsApp (noLoc res) (noLoc arg) | res <- ress, arg <- args ]) [expr] args -- TODO fishy information loss here on the Sym -> expr conversion; we may need to keep the bindings from any partials, even if it's terminal. This might be temporary anyways
      unravel1 v = reduce_deep branch v args
      unravel :: [HsExpr Id] -> [Sym]
      unravel = concatMap (flip (reduce_deep branch) args)
      fail = error $ constr_ppr expr
      -- . uncurry zip . ( -- over all new expressions from reduce1
      --     repeat . (flip update_head branch) . second . (union_sym_tables.) . flip (:) . pure -- make many copies of the branch unioned with the new binds from reduce1
      --     *** id -- BOOKMARK: fix this error
      --   ) -- what happens when reduce1 is identity? Then it's thrown into reduce_deep again which matches against this. It's a similar story with `iterate`, but I think when it converges to a fixed point, somehow it stops?
        -- no, we need to be explicit because GHC isn't going to detect all cycles, even if we're applying a function over and over again to the same argument.
        -- not true, GHC can detect the cycle when the thunk is reforced. I need it to be the same thunk. The problem is that `reduce_deep` and `reduce1` interact.
  in case expr of
    HsLamCase mg -> reduce_deep branch (HsLam mg) args
    
    HsLam mg | let loc = getLoc $ mg_alts mg -- <- NB this is why the locations of MatchGroups don't matter
             , not $ loc `elem` map fst branch -> -- beware about `noLoc`s showing up here: maybe instead break out the pattern matching code
      if matchGroupArity mg > length args
        then terminal
        else
          let pat_matches :: SymTable
              pat_matches =
                union_sym_tables $ (unLoc $ mg_alts mg) & concatMap ( -- over function body alternatives
                  map ( -- over arguments
                    union_sym_tables . map ( -- over possible expressions
                      uncurry (pat_match branch) -- share the same branch
                    ) . (uncurry zip) . (id *** repeat)
                  ) . zip args . map unLoc . m_pats . unLoc -- `args` FINALLY USED HERE
                )
              
              next_explicit_binds = grhs_binds branch mg
              next_exprs = grhs_exprs mg
              next_frame = (loc, union_sym_tables [next_explicit_binds, pat_matches])
              next_branch = next_frame : branch
              next_args = drop (matchGroupArity mg) args
          in concatMap (flip (reduce_deep next_branch) next_args) next_exprs
          
    HsVar (L _ v) | Just left_exprs <- branch_lookup v branch ->
      let flatten :: [(StackBranch, [a])] -> (StackBranch, [a])
          flatten = foldr (\(a, b) (a', b') -> (union_branches [a, a'], b ++ b')) ([], []) -- sometimes pointfree isn't worth it
          -- flatten = foldr (uncurry (***) . (((union_branches.) . flip (:) . pure) *** (++))) ([], []) -- not going to lie, the point-free here is a bit ridiculous
          nf_left = concatMap (flip (reduce_deep branch) args) left_exprs -- TODO The whole StackBranch structure is a little screwy, because all of them should eventually lead to lambdas except for unresolvable bindings. Therefore, 
      in foldr ((++) . flip (reduce_deep branch) args) [] nf_left
    HsVar _ -> terminal
      
    HsApp _ _ ->
      let (fun, next_args) = deapp expr
          passthrough = reduce_deep branch fun (map pure next_args ++ args)
      in case unHsWrap fun of
        HsConLikeOut _ -> terminal
        _ -> passthrough
      
    OpApp (L _ l) (L _ op) _ (L _ r) -> reduce_deep branch op ([l]:[r]:args)
    
    -- Wrappings
    HsWrap _ v -> unravel1 v
    NegApp (L _ v) _ -> unravel1 v
    HsPar (L _ v) -> unravel1 v
    SectionL (L _ v) (L _ op) -> reduce_deep branch op ([v] : args)
    SectionR (L _ m_op) (L _ v) ->
      let (HsVar (L _ op)) = unHsWrap m_op
      in case branch_lookup op branch of
        Just branch_exprs -> branch_exprs & foldr (\(HsLam mg) -> (++(reduce_deep branch (HsLam (mg_flip mg)) ([v] : args)))) [] -- BOOMARK: also do the operator constructor case
        Nothing -> terminal
    -- Take the mapping from the function, reduce_deep'd to HsLam, then pat-match against all arguments
    -- Or, rearrange to an application of `flip` on the app, then the section. This feels way nicer, but the user is just not allowed to rename `flip`, which is unreasonable.
    HsCase l_x@(L _ x) mg -> reduce_deep branch (HsApp (L (getLoc $ mg_alts mg) (HsLam mg)) l_x) args -- refactor as HsLam so we can just use that pat match code
    HsIf _ (L _ if_) (L _ then_) (L _ else_) -> unravel [then_, else_]
    HsMultiIf ty rhss ->
      let next_explicit_binds = grhs_binds branch rhss
          next_exprs = grhs_exprs rhss
          next_frame = (noSrcSpan, next_explicit_binds)
      in concatMap (flip (reduce_deep (next_frame : branch)) args) next_exprs
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
    HsLet _ (L _ expr) -> unravel1 expr -- assume local bindings already caught by surrounding function body (HsLam case)
    -- Terminal forms
  
    HsConLikeOut _ -> terminal
    HsOverLit _ -> terminal
    HsLit _ -> terminal
    ExplicitTuple _ _ -> terminal
    ExplicitSum _ _ _ _ -> terminal
    ExplicitList _ _ _ -> terminal
    ExplicitPArr _ _ -> terminal
    _ -> fail
-- 
-- reduce1 :: StackBranch -> Sym -> Maybe (SymTable, [Sym]) -- only return new and updated entries, stop at names and literals... except I guess at a direct application? That dictates whether or not this is the thing that should update the stack table, or if it should just return a flat symbol table. 
-- reduce1 branch (Sym (_, expr)) = case expr of
  
  
  -- ignore HsVar and HsApp, which should be fulfilled by the calling scope
  -- Note that the table isn't always updated, so we can't rely on it. Instead, we must wrap in Maybe
  -- 