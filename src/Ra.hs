{-# LANGUAGE NamedFieldPuns, LambdaCase, TupleSections, MultiWayIf #-}
module Ra (
  pat_match,
  reduce_deep
) where

import GHC
import DataCon ( dataConName )
import Type ( tyConAppTyConPicky_maybe )
import TyCon ( tyConName )
import ConLike ( ConLike (..) )
import Name ( mkSystemName, nameOccName )
import OccName ( mkVarOcc, occNameString )
import Unique ( mkVarOccUnique )
import FastString ( mkFastString ) -- for WildPat synthesis
import Var ( mkLocalVar ) -- for WildPat synthesis
import IdInfo ( vanillaIdInfo, IdDetails(VanillaId) ) -- for WildPat synthesis

import Data.Coerce ( coerce )
import Data.Char ( isLower )
import Data.Tuple ( swap )
import Data.Tuple.Extra ( second, (***), (&&&), both )
import Data.Function ( (&) )
import Data.Maybe ( fromMaybe, maybeToList, isNothing )
import Data.Data ( toConstr )
import Data.Generics.Extra ( constr_ppr )
import Data.Semigroup ( (<>) )
import Data.Monoid ( mempty, mconcat )
import Control.Monad ( guard )
import Control.Applicative ( (<|>), liftA2 )
import Control.Exception ( assert )

import Data.Map.Strict ( Map(..), unionsWith, unions, unionWith, union, singleton, (!?), (!), foldlWithKey, foldrWithKey, keys, elems, insert, mapWithKey)
import qualified Data.Map.Strict as M ( null, empty )
import qualified Data.Set as S ( fromList )
-- import qualified Data.Set as S ( insert )

import qualified Ra.Refs as Refs
import {-# SOURCE #-} Ra.GHC
import Ra.Lang
import Ra.Extra
import Ra.Refs ( write_funs, read_funs )

-- type NFStackTable = Map Id NF
-- data NF = WHNF (HsExpr Id) | Ref (HsExpr Id)
-- WHNF is either a literal, data construction, or unknown function app;
-- Ref holds the expression that spits out the pipe that holds the value[s] that we must trace in a separate traversal over ref types. Note the Located because we use SrcSpan to find specific write instances

app :: Sym -> [Sym] -> Sym
app = foldl (curry $ Sym False mempty . noLoc . uncurry (HsApp NoExt) . both (expr . coerce)) -- one downside is the noLoc on the app, but all the actual exprs are located

pat_multi_match ::
  (Sym -> Maybe [Sym]) -- predicate and expression expander
  -> StackBranch -- full symbol table
  -> [Pat Id]
  -> Sym
  -> PatMatchSyms
pat_multi_match expand stack pats sym = case expand sym of
  Just args | let arg_matches :: [PatMatchSyms]
                  arg_matches = map (uncurry (pat_match stack)) (zip pats args)
            , and $ map (not . M.null . pms_syms) arg_matches -- TODO this _should_ be fine for matching against nested patterns but just make sure.
            -> mconcat arg_matches -- should be disjoint bindings because the args contribute different variables
  Nothing -> mempty

-- invoke as: `unions . concatMap (map ((unions . concatMap . pat_match table) . unLoc) . zip args . m_pats) mg_alts` on `MatchGroup`'s `mg_alts`
pat_match ::
  StackBranch
  -> Pat Id
  -> Sym
  -> PatMatchSyms -- the new bindings in _this stack frame only_, even if new ones are resolved above and below
-- all new matches from the pat match; M.empty denotes the match failed (we'll bind wildcards under `_` which will be ignored later since it's an illegal variable and function name)
-- Valid HsExpr: HsApp, OpApp, NegApp, ExplicitTuple, ExplicitList, (SectionL, SectionR) (for data types that are named by operators, e.g. `:`; I might not support this in v1 because it's so thin)
-- Valid Pat:
pat_match stack pat sym = case pat of
  -- M.empty
  WildPat ty ->
    let fake_name = mkSystemName (mkVarOccUnique $ mkFastString "_") (mkVarOcc "_")
        fake_var = mkLocalVar VanillaId fake_name ty vanillaIdInfo
    in mempty {
        pms_syms = singleton fake_var [sym]
      }
  -- wrapper
  LazyPat _ (L _ pat) -> pat_match stack pat sym
  ParPat _ (L _ pat) -> pat_match stack pat sym
  BangPat _ (L _ pat) -> pat_match stack pat sym
  -- SigPatOut (L _ pat) _ -> pat_match stack pat sym
  -- base
  VarPat _ (L _ v) -> mempty {
      pms_syms = singleton v [sym]
    }
  LitPat _ -> mempty -- no new name bindings
  NPat _ _ _ _ -> mempty
  -- container
  ListPat pats _ _ -> mconcat $ map (\(L _ pat') -> pat_match stack pat' sym) pats -- encodes the logic that all elements of a list might be part of the pattern regardless of order
  AsPat (L _ bound) (L _ pat') -> mempty { pms_syms = singleton bound [sym] } <> pat_match stack pat' sym -- NB this should also be disjoint (between the binding and the internal pattern); just guard in case
  TuplePat pats _ _ ->
    let nf_syms = reduce_deep stack [] sym
        matcher sym = case to_expr sym of 
            ExplicitTuple args _ -> Just (map (fmap (\(Present (L _ expr')) -> expr')) args)
            _ -> Nothing
    in mconcat $ map (pat_multi_match matcher stack (map unLoc pats)) (rs_syms nf_syms)
      
  ConPatOut{ pat_con = L _ (RealDataCon pat_con'), pat_args = d_pat_args } -> case d_pat_args of
    PrefixCon pats ->
      let matcher x | (HsConLikeOut (RealDataCon con), args) <- deapp x -- x is in NF thanks to pat_multi_match; this assumes it
                    , dataConName con == dataConName pat_con' = Just args
                    | otherwise = Nothing
          nf_exprs = reduce_deep stack [] sym
      in mconcat $ map (pat_multi_match matcher stack (map unLoc pats)) (rs_syms nf_exprs)
    
    -- case sym of
    --   HsVar id | varName id == dataConName pat_con -> 
    --   HsApp l r -> 
    --     let fst $ iterate (\(l, args) -> case l of
    --       HsApp l' r' -> (l', (r' : args))
    --       HsCase mg ->  -- need to update the symbol table after pattern matching! Normally, it would be great to have that function that spits back the new symbol table and the tree of expressions. Then it should be a separate function that calls patterns matching. I forget why now I wanted to have it all done within pattern match. We already had the idea for this function. It drills all the way through args.
    --       _ -> )
    --   HsCase -> 
    --   let tied = tie sym
    --   in unions $ map (deapp . bool () (tie (table))) (snd tied)
    RecCon _ -> error "Record syntax yet to be implemented"
  _ -> error $ constr_ppr pat

reduce_deep :: Stack -> [[Sym]] -> Sym -> ReduceSyms
reduce_deep _ args@(_:_) (L _ (HsConLikeOut _ _)) = error "Only bare ConLike should make it to `reduce_deep`" -- $ (map constr_ppr args) ++ 
reduce_deep _ (_:_) sym | is_zeroth_kind sym = error "Application on " ++ (show $ toConstr $ to_expr sym)

reduce_deep stack args sym =
  -------------------
  -- SYM BASE CASE --
  -------------------
  let terminal =
        -- assert (isNothing m_parts) $
        (((flip ReduceSyms mempty . pure) *** ((++args) . map pure)) $ deapp sym) -- add all arguments to the manual arguments in `reduce_deep`'s... uhh, arguments.
        & (uncurry $
            foldl (\ress args' ->
                let nf_args' = mconcat $ map (reduce_deep stack []) args'
                in ReduceSyms {
                    rs_syms = [ Sym {
                        expr = noLoc $ HsApp NoExt res (expr arg),
                        stack_loc = make_stack_key stack,
                        is_consumed = False
                      } | res <- rs_syms ress, arg <- rs_syms nf_args' ], -- same issue as HsApp reduce rule: noLoc on the apps but all exprs are loc'd
                    rs_writes = unionWith (++) (rs_writes ress) (rs_writes nf_args')
                  }
              )
          ) -- TODO fishy information loss here on the Sym -> expr conversion; we may need to keep the bindings from any partials, even if it's terminal. This might be temporary anyways -- thinking about this, i don't think it's a problem because the terminal HsApps are unresolved names that should never be unravelled
      unravel1 :: Sym -> ReduceSyms
      unravel1 = reduce_deep stack args
      
      unravel :: [Sym] -> ReduceSyms
      unravel = mconcat . map unravel1
      fail = error $ constr_ppr sym
      -- . uncurry zip . ( -- over all new expressions from reduce1
      --     repeat . (flip update_head stack) . second . (union_sym_tables.) . flip (:) . pure -- make many copies of the stack unioned with the new binds from reduce1
      --     *** id -- BOOKMARK: fix this error
      --   ) -- what happens when reduce1 is identity? Then it's thrown into reduce_deep again which matches against this. It's a similar story with `iterate`, but I think when it converges to a fixed point, somehow it stops?
        -- no, we need to be explicit because GHC isn't going to detect all cycles, even if we're applying a function over and over again to the same argument.
        -- not true, GHC can detect the cycle when the thunk is reforced. I need it to be the same thunk. The problem is that `reduce_deep` and `reduce1` interact.
  in case expr sym of
    HsLamCase _ mg -> reduce_deep stack args (HsLam mg)
    
    HsLam _ mg | let loc = getLoc $ mg_alts mg -- <- NB this is why the locations of MatchGroups don't matter
             , not $ is_visited stack loc -> -- beware about `noLoc`s showing up here: maybe instead break out the pattern matching code
      if matchGroupArity mg > length args
        then terminal
        else
          let pat_matches =
                (unLoc $ mg_alts mg) & mconcat . mconcat . map ( -- over function body alternatives
                  map ( -- over arguments
                    mconcat . map ( -- over possible expressions
                      uncurry (flip (pat_match (st_branch stack))) -- share the same stack
                    ) . (uncurry zip) . (id *** repeat)
                  ) . zip args . map unLoc . m_pats . unLoc -- `args` FINALLY USED HERE
                )
              
              PatMatchSyms next_explicit_binds bind_writes = grhs_binds (st_branch stack) mg
              next_exprs = grhs_exprs $ map (grhssGRHSs . m_grhss . unLoc) $ unLoc $ mg_alts mg
              next_frame = (loc, union_sym_tables [pms_syms pat_matches, next_explicit_binds])
              next_stack = stack {
                  st_branch = SB $ second (next_frame:) $ coerce $ st_branch stack
                }
              next_args = drop (matchGroupArity mg) args
          in mempty { rs_writes = bind_writes <> pms_writes pat_matches } <> (mconcat $ map (reduce_deep next_stack next_args) next_exprs)
          
    HsVar _ (L loc v) ->
      let args' | a : rest <- args
                , Just "Consumer" <- (occNameString <$> nameOccName <$> tyConName <$> (tyConAppTyConPicky_maybe $ varType v))
                  = (map (\b -> b { is_consumed = True }) a) : rest -- identify as consumer-consumed values
                | otherwise = args
      in (\rs@(ReduceSyms { rs_syms }) -> -- enforce nesting rule: all invokations on consumed values are consumed
          rs { rs_syms = map (\sym'@(Sym { is_consumed = is_consumed' }) ->
              sym' { is_consumed = is_consumed' || is_consumed sym })
            rs_syms }
        ) $
        if | Just left_exprs <- stack_var_lookup True v stack -> -- this absolutely sucks, we have to use the "soft" search because instance name Uniques are totally unusable. Can't even use `Name`, unless I convert to string every time... which I might need to do in the future for performance reasons if I can't come up with a solution for this. 
            mconcat $ map (reduce_deep stack args) left_exprs
      -- in foldr ((++) . flip (reduce_deep stack) args) [] nf_left
           | otherwise -> case varString v of
            ------------------------------------
            -- *** SPECIAL CASE FUNCTIONS *** --
            ------------------------------------
            
            -- "newEmptyMVar" -> -- return as terminal and identify above
            -- "newMVar" -> -- find this in post-processing and do it
            -- "takeMVar" -> if length args >= 1 -- no need, do this in post-processing
            --   then 
            --   else terminal
            
            -- MAGIC MONADS (fallthrough)
            ">>" | i:o:_ <- args
                 , let i' = map unravel1 i
                       o' = map unravel1 o -> -- magical monad `*>` == `>>`: take right-hand syms, merge writes
                  mconcat [i'' { rs_syms = mempty } <> o'' | i'' <- i', o'' <- o'] -- combinatorial EXPLOSION! BOOM PEW PEW
            ">>=" | i:o:args' <- args -> -- magical monad `>>=`: shove the return value from the last stage into the next, merge writes
                  -- grabbing the writes is as easy as just adding `i` to the arguments; the argument resolution in `terminal` will take care of it
                  -- under the assumption that it's valid to assume IO is a pure wrapper, this actually just reduces to plain application of a lambda
                    reduce_deep stack i:args' o
              
            "forkIO" | to_fork:rest <- args -> 
                let next_stack = stack {
                        st_threads = (length $ coerce $ st_branch stack) : st_threads, -- TODO wait, where was I going with this?
                        st_branch = SB $ ((loc, M.empty):) $ coerce $ st_branch stack
                      }
                    result = mconcat . map (reduce_deep next_stack rest) mempty to_fork
                in result {
                    rs_syms = [error "Using the ThreadID from forkIO is not yet supported."]
                  }
            "putMVar" -> if length args >= 2
              then
                let (pipes:vals:_) = args
                in ReduceSyms {
                    rs_syms = terminal,
                    rs_writes = unionsWith (++) [singleton pipe (make_thread_key stack, arg) | pipe <- pipes, arg <- args]
                  }
              else terminal
            _ -> terminal
      
    HsApp _ _ _ -> -- this should only come up from the GHC AST, not from our own reduce-unwrap-wrap
      let (fun, next_args) = deapp sym
          passthrough = reduce_deep stack (map pure next_args ++ args) fun
      in case to_expr $ unHsWrap fun of
        HsConLikeOut _ _ -> terminal
        _ -> passthrough
      
    OpApp l_l l_op _ l_r -> reduce_deep stack ([l_l]:[l_r]:args) l_op
    
    -- Wrappings
    HsWrap _ v -> unravel1 v
    NegApp _ (L _ v) _ -> unravel1 v
    HsPar _ (L _ v) -> unravel1 v
    SectionL _ (L _ v) (L _ op) -> reduce_deep stack ([v] : args) op
    SectionR _ m_op (L _ v) ->
      let (HsVar (L _ op)) = to_expr $ unHsWrap m_op
      in case stack_var_lookup op stack of
        Just branch_exprs -> branch_exprs & foldr (<>(reduce_deep stack ([v] : args) . fmap (\(HsLam mg) -> HsLam (mg_flip mg)))) mempty -- BOOMARK: also do the operator constructor case
        Nothing -> terminal
    -- Take the mapping from the function, reduce_deep'd to HsLam, then pat-match against all arguments
    -- Or, rearrange to an application of `flip` on the app, then the section. This feels way nicer, but the user is just not allowed to rename `flip`, which is unreasonable.
    HsCase _ l_x@(L _ x) mg -> unravel1 (noLoc $ HsApp (L (getLoc $ mg_alts mg) (HsLam mg)) l_x) -- refactor as HsLam so we can just use that pat match code
    HsIf _ (L _ if_) (L _ then_) (L _ else_) -> unravel [then_, else_]
    HsMultiIf _ ty rhss ->
      let PatMatchSyms next_explicit_binds bind_writes = grhs_binds stack rhss
          next_exprs = grhs_exprs rhss
          next_frame = (noSrcSpan, next_explicit_binds)
      in mempty { rs_writes = bind_writes } <> (mconcat $ map (reduce_deep (next_frame : stack) args) next_exprs)
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
    HsDo _ (L _ stmts) _ -> stmts & foldl (\syms stmt -> case stmt of
        LastStmt expr _ _ ->
          let exprs' = unravel1 expr
          in syms { rs_syms = mempty }
              <> exprs' {
                rs_syms = rs_syms exprs' & map (\expr' ->
                    let (m_fun, args) = deapp expr'
                        fun = to_expr m_fun
                    in if varString fun == "return"
                          && length args > 0 -- ensure that it's saturated to avoid pathological case of `return return`, i.e. `IO (a -> IO a)`
                      then head args -- `return` is unambiguously unfolded into the constituent -- BOOKMARK this isn't the place to do this analysis: unpack in the HsApp case, or in the post-processing. This does need to happen -- it's the only way that we can interpret the values going from other monads or pure land into IO, and also accompanied with the IORef cases.
                      else HsApp runIO_var (unravel1 arg1)
                  ) }-- kill the results from all previous stmts because of the semantics of `>>`
        -- ApplicativeStmt _ _ _ -> undefined -- TODO yet to appear in the wild and be implemented
        -- BindStmt pat expr _ _ ty ->  -- covered by binds; can't be the last statement anyways -- <- scratch that -- TODO implement this to unbox the monad (requires fake IO structure2)
        BodyStmt expr _ _ _ -> unravel1 expr
        ParStmt -> undefined -- not analyzed for now, because the list comp is too niche (only used for parallel monad comprehensions; see <https://gitlab.haskell.org/ghc/ghc/wikis/monad-comprehensions>)
        -- fun fact: I thought ParStmt was for "parenthesized", but it's "parallel"
      ) [] -- shove all the work to another round of `reduce_deep`.
    
    -- Terminal forms
  
    HsConLikeOut _ -> terminal
    HsOverLit _ -> terminal
    HsLit _ -> terminal
    ExplicitTuple _ _ -> terminal
    ExplicitSum _ _ _ _ -> terminal
    ExplicitList _ _ _ -> terminal
    -- ExplicitPArr _ _ -> terminal
    _ -> fail


-- get_writes :: Branch -> Stmt Id Id (HsExpr Id) -> Writes
-- get_writes stack stmt = case stmt of
  
    
-- 
-- reduce1 :: StackBranch -> Sym -> Maybe (SymTable, [Sym]) -- only return new and updated entries, stop at names and literals... except I guess at a direct application? That dictates whether or not this is the thing that should update the stack table, or if it should just return a flat symbol table. 
-- reduce1 stack (Sym (_, expr)) = case expr of
  
  
  -- ignore HsVar and HsApp, which should be fulfilled by the calling scope
  -- Note that the table isn't always updated, so we can't rely on it. Instead, we must wrap in Maybe
  --