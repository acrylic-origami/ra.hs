{-# LANGUAGE NamedFieldPuns, LambdaCase, TupleSections, MultiWayIf #-}
module Ra (
  pat_match,
  reduce_deep,
  reduce
) where

import GHC
import DataCon ( dataConName )
import TyCon ( tyConName )
import ConLike ( ConLike (..) )
import Name ( mkSystemName, nameOccName )
import OccName ( mkVarOcc, occNameString )
import Unique ( mkVarOccUnique )
import FastString ( mkFastString ) -- for WildPat synthesis
import SrcLoc ( noSrcSpan )
import Var ( mkLocalVar ) -- for WildPat synthesis
import IdInfo ( vanillaIdInfo, IdDetails(VanillaId) ) -- for WildPat synthesis

import Data.Coerce ( coerce )
import Data.Char ( isLower )
import Data.Tuple ( swap )
import Data.Tuple.Extra ( first, second, (***), (&&&), both )
import Data.Function ( (&) )
import Data.Maybe ( catMaybes, fromMaybe, maybeToList, isNothing )
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

-- type NFStackTable = Map GhcTc NF
-- data NF = WHNF (HsExpr GhcTc) | Ref (HsExpr GhcTc)
-- WHNF is either a literal, data construction, or unknown function app;
-- Ref holds the expression that spits out the pipe that holds the value[s] that we must trace in a separate traversal over ref types. Note the Located because we use SrcSpan to find specific write instances

-- app :: Sym -> [Sym] -> Sym
-- app = foldl (curry $ Sym False mempty . noLoc . uncurry (HsApp undefined) . both (expr . coerce)) -- one downside is the noLoc on the app, but all the actual exprs are located

pat_multi_match ::
  Stack -- full symbol table
  -> [Pat GhcTc]
  -> [[SymApp]]
  -> Maybe PatMatchSyms
pat_multi_match stack pats args | let matches = map (uncurry ((mconcat.) . map . pat_match stack)) (zip pats args)
                                , and $ map (not . M.null . pms_syms) matches
                                  = Just $ mconcat matches -- filter (not . M.null . pms_syms) $ map (uncurry (pat_match stack)) zipped_pat_args
                                      
                                | otherwise = Nothing

-- invoke as: `unions . concatMap (map ((unions . concatMap . pat_match table) . unLoc) . zip args . m_pats) mg_alts` on `MatchGroup`'s `mg_alts`
pat_match ::
  Stack
  -> Pat GhcTc
  -> SymApp
  -> PatMatchSyms -- the new bindings in _this stack frame only_, even if new ones are resolved above and below
-- all new matches from the pat match; M.empty denotes the match failed (we'll bind wildcards under `_` which will be ignored later since it's an illegal variable and function name)
-- Valid HsExpr: HsApp, OpApp, NegApp, ExplicitTuple, ExplicitList, (SectionL, SectionR) (for data types that are named by operators, e.g. `:`; I might not support this in v1 because it's so thin)
-- Valid Pat:
pat_match _ pat sa =
  let nf_syms = reduce_deep stack sa
  in PatMatchSyms {
      pms_syms = foldr (flip M.insert (rs_syms nf_syms)) M.empty $ everything (++) ([] `mkQ` ((\(HsVar _ (L _ v)) -> [v]) :: HsExpr GhcTc -> Id)) pat
      pms_writes = rs_writes nf_syms
    }
    
-- pat_match stack pat sa =
--   let nf_syms = reduce_deep stack sa
--   in case pat of
--     -- M.empty
--     WildPat ty ->
--       let fake_name = mkSystemName (mkVarOccUnique $ mkFastString "_") (mkVarOcc "_")
--           fake_var = mkLocalVar VanillaId fake_name ty vanillaIdInfo
--       in PatMatchSyms {
--           pms_syms = singleton fake_var (rs_syms nf_syms),
--           pms_writes = rs_writes nf_syms
--         }
--     -- wrapper
--     LazyPat _ (L _ pat) -> pat_match stack pat sa
--     ParPat _ (L _ pat) -> pat_match stack pat sa
--     BangPat _ (L _ pat) -> pat_match stack pat sa
--     -- SigPatOut (L _ pat) _ -> pat_match stack pat sa
--     -- base
--     VarPat _ (L _ v) -> PatMatchSyms {
--         pms_syms = singleton v (rs_syms nf_syms),
--         pms_writes = rs_writes nf_syms
--       }
--     LitPat _ _ -> mempty -- no new name bindings
--     NPat _ _ _ _ -> mempty
--     -- container
--     ListPat _ pats -> mconcat $ map (\(L _ pat') -> pat_match stack pat' sa) pats -- encodes the logic that all elements of a list might be part of the pattern regardless of order
--     AsPat _ (L _ bound) (L _ pat') -> mempty { pms_syms = singleton bound [sa] } <> pat_match stack pat' sa -- NB this should also be disjoint (between the binding and the internal pattern); just guard in case
--     TuplePat _ pats _ ->
--       let matcher (SA _ (x:_)) = error "Argument on explicit tuple. Perhaps a tuple section, which isn't supported yet."
--           matcher (SA sym' []) = case unLoc $ expr sym' of
--             ExplicitTuple _ args'' _ ->
--               pat_multi_match stack (map unLoc pats) $ map ((\case
--                   Present _ expr' -> [SA ((sa_sym sa) { expr = expr' }) []] -- NB encodes the assumption that we should preserve the original location of creation for this object, rather than this unravelling point because the datatype decompositions are trivial and can't define an object's identity
--                   Missing _ -> error "Tuple sections aren't supported yet."
--                 ) . unLoc) args''
--             _ -> mempty
--           next_pms = mconcat $ catMaybes $ map matcher (rs_syms nf_syms)
--       in append_pms_writes (rs_writes nf_syms) next_pms
        
--     ConPatOut{ pat_con = L _ (RealDataCon pat_con'), pat_args = d_pat_args } -> case d_pat_args of
--       PrefixCon pats ->
--         let matcher (SA sym' args') | (L _ (HsConLikeOut _ (RealDataCon con)), args'') <- deapp (expr sym') -- sym' is in NF thanks to pat_multi_match; this assumes it
--                                     , dataConName con == dataConName pat_con'
--                                       = let flat_args = ((map (\arg'' -> pure $ SA (sym' { expr = arg'' }) []) args'') ++ args') -- [[SymApp]]
--                                         in pat_multi_match stack (map unLoc pats) flat_args
--                                     | otherwise = mempty
--             next_pms = mconcat $ catMaybes $ map matcher (rs_syms nf_syms)
--         in append_pms_writes (rs_writes nf_syms) next_pms
        
--       RecCon _ -> error "Record syntax yet to be implemented"
--     _ -> error $ constr_ppr pat

reduce :: SymTable -> LHsExpr GhcTc -> ReduceSyms -- symtable for ambient declarations
reduce table expr = reduce_deep (mempty { st_branch = SB [(noSrcSpan, table)] }) (SA (Sym False [] expr) [])
-- reduce = curry $ uncurry (flip reduce_deep) . (flip SA [] . Sym False [] *** SB . pure . (noLoc,)) -- yeah, sometimes pointfree ain't worth it

reduce_deep :: Stack -> SymApp -> ReduceSyms
reduce_deep _ sa | let args = sa_args sa
                       sym = sa_sym sa
                 , length args > 0 && is_zeroth_kind sym = error $ "Application on " ++ (show $ toConstr $ expr sym)
reduce_deep stack sa@(SA sym args) =
  -------------------
  -- SYM BASE CASE --
  -------------------
  let terminal =
        let nf_args args' = 
              let args'' = map (map (reduce_deep stack)) args' -- [[ ([SymApp], Writes) ]], to become ([[SymApp]], Writes)
                  extract :: Monoid a => (ReduceSyms -> a) -> [a]
                  extract f = map (mconcat . map f) args''
              in (extract rs_syms, mconcat $ extract rs_writes) -- NOTE the detachment of sym from write. Hopefully that isn't eventually an issue.
        in uncurry ReduceSyms $ first (\args' -> [sa { sa_args = args' }]) $ nf_args args
      
      unravel1 :: LHsExpr GhcTc -> [[LHsExpr GhcTc]] -> ReduceSyms -- peeling back wrappings; consider refactor to evaluate most convenient type to put here
      unravel1 target new_args = reduce_deep stack $ SA {
          sa_sym = sym {
              expr = target
            },
          sa_args = (map (map (\arg -> SA sym { expr = arg } [])) new_args ++ args) -- NB `consumed` law: `is_consumed` property at least distributes over App; if the leftmost var is of type `Consumer`, then it might make some args `consumed` as well.
        }
      
      mksym = Sym False (make_stack_key stack)
      mklocsym = flip Sym (make_stack_key stack)
      
      fail = error $ "FAIL" ++ (constr_ppr $ expr $ sym)
  in case unLoc $ expr sym of
    HsLamCase _ mg -> unravel1 (HsLam undefined mg <$ expr sym) []
    
    HsLam _ mg | let loc = getLoc $ mg_alts mg -- <- NB this is why the locations of MatchGroups don't matter
             , not $ is_visited stack loc -> -- beware about `noLoc`s showing up here: maybe instead break out the pattern matching code
      if matchGroupArity mg > length args
        then terminal
        else
          let pat_matches =
                (unLoc $ mg_alts mg) & mconcat . mconcat . map ( -- over function body alternatives
                  map ( -- over arguments
                    mconcat . map ( -- over possible expressions
                      uncurry (flip (pat_match stack)) -- share the same stack
                    ) . (uncurry zip) . (id *** repeat)
                  ) . zip (sa_args sa) . map unLoc . m_pats . unLoc -- `args` FINALLY USED HERE
                )
              
              PatMatchSyms next_explicit_binds bind_writes = grhs_binds stack mg
              next_exprs = grhs_exprs $ map (grhssGRHSs . m_grhss . unLoc) $ unLoc $ mg_alts mg
              next_frame = (loc, union_sym_tables [pms_syms pat_matches, next_explicit_binds])
              next_stack = stack {
                  st_branch = SB (next_frame : (coerce $ st_branch stack))
                }
              next_args = drop (matchGroupArity mg) args
          in mempty { rs_writes = bind_writes <> pms_writes pat_matches } <> (mconcat $ map (\next_expr -> reduce_deep next_stack $ SA { sa_sym = sym { expr = next_expr }, sa_args =  next_args }) next_exprs) -- TODO check if the sym record update + args are correct for this stage
          
    HsVar _ (L loc v) ->
      let args' | a:rest <- args
                , Just "Consumer" <- varTyConName v
                  = (map (\b -> b { sa_sym = (sa_sym b) { is_consumed = True } }) a) : rest -- identify as consumer-consumed values
                | otherwise = args
      in (\rs@(ReduceSyms { rs_syms }) -> -- enforce nesting rule: all invokations on consumed values are consumed
          rs {
              rs_syms = map (\sa' -> sa' { sa_sym = (sa_sym sa') { is_consumed = is_consumed (sa_sym sa') || is_consumed sym } }) rs_syms
            }
        ) $
        if | varString v == "debug#" ->
              -- DEBUG SYMBOL
              mempty
           | Just left_syms <- stack_var_lookup True v stack -> -- this absolutely sucks, we have to use the "soft" search because instance name Uniques are totally unusable. Can't even use `Name`, unless I convert to string every time... which I might need to do in the future for performance reasons if I can't come up with a solution for this. 
            mconcat $ map (\sa' -> reduce_deep stack $ sa' { sa_args = sa_args sa' ++ args' }) left_syms
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
            "return" | vs:args'' <- args' -> mconcat $ map (\sa' -> reduce_deep stack $ sa' { sa_args = args'' }) vs
            -- NB about `[]` on the rightmost side of the pattern match on `args'`: it's never typesafe to apply to a monad (except `Arrow`), so if we see arguments, we have to freak out and not move forward with that.
            ">>" | i:o:[] <- args'
                 , let i' = map (reduce_deep stack) i
                       o' = map (reduce_deep stack) o -> -- magical monad `*>` == `>>`: take right-hand syms, merge writes
                  mconcat [i'' { rs_syms = mempty } <> o'' | i'' <- i', o'' <- o'] -- combinatorial EXPLOSION! BOOM PEW PEW
            ">>=" | i:o:[] <- args' -> -- magical monad `>>=`: shove the return value from the last stage into the next, merge writes
                  -- grabbing the writes is as easy as just adding `i` to the arguments; the argument resolution in `terminal` will take care of it
                  -- under the assumption that it's valid to assume IO is a pure wrapper, this actually just reduces to plain application of a lambda
                    mconcat $ map (\fun -> reduce_deep stack fun {
                          sa_args = sa_args fun ++ [i]
                        }
                      ) o
              
            "forkIO" | to_fork:rest <- args' -> 
                let next_stack = stack {
                        st_threads = (length $ unSB $ st_branch stack) : st_threads stack,
                        st_branch = SB $ ((loc, M.empty):) $ coerce $ st_branch stack
                      }
                    result = mconcat $ map (\sa' -> reduce_deep next_stack $ SA (sa_sym sa') (sa_args sa' ++ rest)) to_fork
                in result {
                    rs_syms = [error "Using the ThreadID from forkIO is not yet supported."]
                  }
            "putMVar" -> if length args' >= 2
              then
                let (pipes:vals:_) = args'
                in terminal {
                    rs_writes = rs_writes terminal <> unionsWith (++) [
                        singleton (unLoc pipe_id, stack_loc $ sa_sym m_pipe) [(make_thread_key stack, val)]
                          | m_pipe <- pipes
                          , val <- vals
                          , (HsVar _ pipe_id) <- [unLoc $ expr $ sa_sym m_pipe] -- hax? o/w not sure how to pattern match in a list comprehension
                      ]
                  }
              else terminal
            _ -> terminal
      
    HsApp _ _ _ -> -- this should only come up from the GHC AST, not from our own reduce-unwrap-wrap
      let (fun, next_args) = deapp $ expr sym
          passthrough = unravel1 fun (map pure next_args)
      in case unLoc fun of
        HsConLikeOut _ _ -> terminal
        _ -> passthrough
      
    OpApp _ l_l l_op l_r -> unravel1 l_op [[l_l], [l_r]]
    
    -- Wrappings
    HsWrap _ _ v -> unravel1 (const v <$> expr sym) [] -- why is HsWrap wrapping a bare HsExpr?! No loc? Inferred from surroundings I guess (like this)
    NegApp _ v _ -> unravel1 v []
    HsPar _ v -> unravel1 v []
    SectionL _ v m_op -> unravel1 m_op [[v]]
    SectionR _ m_op v ->
      let L _ (HsVar _ op) = unHsWrap m_op
      in case stack_var_lookup True (unLoc op) stack of
        Just branch_exprs -> mconcat $ map (\sa' ->
            reduce_deep stack $ SA {
                sa_sym = (sa_sym sa') {
                    expr = (\(HsLam x mg) -> HsLam x (mg_flip mg)) <$> (expr $ sa_sym sa')
                  },
                sa_args = [[sa { sa_sym = sym { expr = v } }]] ++ (sa_args sa') ++ args -- TODO also do the operator constructor case -- TODO check that `sym` record update is the right thing to do here
              }
          ) branch_exprs
        Nothing -> terminal
        
    HsCase _ x mg -> unravel1 (noLoc $ HsApp NoExt (HsLam NoExt mg <$ mg_alts mg) x) [] -- refactor as HsLam so we can just use that pat match code
    HsIf _ _ if_ then_ else_ -> unravel1 then_ [] <> unravel1 else_ []
    HsMultiIf ty rhss ->
      let PatMatchSyms next_explicit_binds bind_writes = grhs_binds stack rhss
          next_exprs = grhs_exprs rhss
          next_frame = (noSrcSpan, next_explicit_binds)
      in mempty { rs_writes = bind_writes } <> (mconcat $ map (\next_expr -> reduce_deep (stack { st_branch = mapSB (next_frame:) (st_branch stack) }) (sa { sa_sym = sym { expr = next_expr } })) next_exprs) -- TODO check that record update with sym (and its location) is the right move here
      
    HsLet _ _ expr -> unravel1 expr [] -- assume local bindings already caught by surrounding function body (HsLam case)
    HsDo _ _ (L _ stmts) -> foldl (\syms (L _ stmt) ->
        case stmt of
          LastStmt _ expr _ _ -> syms { rs_syms = mempty } <> unravel1 expr [] -- kill the results from all previous stmts because of the semantics of `>>`
          -- ApplicativeStmt _ _ _ -> undefined -- TODO yet to appear in the wild and be implemented
          BindStmt pat expr _ _ ty -> syms -- covered by binds; can't be the last statement anyways -- <- scratch that -- TODO implement this to unbox the monad (requires fake IO structure2) -- <- scratch THAT, we're not going to do anything because the binds are covered in grhs_binds; we're letting IO and other magic monads be unravelled into their values contained within to simplify analysis
          LetStmt _ _ -> syms -- same story as BindStmt
          BodyStmt _ expr _ _ -> syms { rs_syms = mempty } <> unravel1 expr []
          ParStmt _ _ _ _ -> undefined -- not analyzed for now, because the list comp is too niche (only used for parallel monad comprehensions; see <https://gitlab.haskell.org/ghc/ghc/wikis/monad-comprehensions>)
          _ -> fail
          -- fun fact: I thought ParStmt was for "parenthesized", but it's "parallel"
      ) mempty stmts -- push all the work to another round of `reduce_deep`.
    
    -- Terminal forms
    
    HsConLikeOut _ _ -> if length args == 0 then terminal else error "Only bare ConLike should make it to `reduce_deep`" 
    HsOverLit _ _ -> terminal
    HsLit _ _ -> terminal
    ExplicitTuple _ _ _ -> terminal
    ExplicitSum _ _ _ _ -> terminal
    ExplicitList _ _ _ -> terminal
    -- ExplicitPArr _ _ -> terminal
    _ -> error ("Incomplete coverage of HsExpr rules: encountered " ++ (show $ toConstr $ expr sym))