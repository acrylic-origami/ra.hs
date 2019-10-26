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

import Data.List ( elemIndex )
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

import Data.Map.Strict ( Map(..), unionsWith, unions, unionWith, union, singleton, (!?), (!), foldlWithKey, foldrWithKey, keys, elems, mapWithKey, assocs)
import qualified Data.Map.Strict as M ( null, member, empty, insert, map )
import Data.Set ( Set(..), intersection, difference, (\\) )
import qualified Data.Set as S ( fromList, member, insert )
-- import qualified Data.Set as S ( insert )

import qualified Ra.Refs as Refs
import {-# SOURCE #-} Ra.GHC
import Ra.Lang
import Ra.Extra
import Ra.Refs ( write_funs, read_funs )

pat_multi_match ::
  [Pat GhcTc]
  -> [[SymApp]]
  -> Maybe PatMatchSyms
pat_multi_match pats args =
  let matches = map (uncurry ((mconcat.) . map . pat_match)) (zip pats args)
  in foldl1 (<>) matches

pat_match ::
  Pat GhcTc
  -> SymApp
  -> Maybe PatMatchSyms
pat_match pat sa =
  let nf_syms = reduce_deep sa
  in case pat of
    ---------------------------------
    -- *** UNWRAPPING PATTERNS *** --
    ---------------------------------
    WildPat ty -> Just $ mempty { pms_writes = rs_writes nf_syms } -- TODO check if this is the right [write, haha] behavior
      
    -- Wrappers --
    LazyPat _ (L _ pat) -> pat_match pat sa
    ParPat _ (L _ pat) -> pat_match pat sa
    BangPat _ (L _ pat) -> pat_match pat sa
    -- SigPatOut (L _ pat) _ -> pat_match pat sa
    
    -- Bases --
    VarPat _ (L _ v) -> Just $ mempty {
        pms_syms = singleton v (rs_syms nf_syms),
        pms_writes = rs_writes nf_syms
      }
    LitPat _ _ -> Just mempty -- no new name bindings
    NPat _ _ _ _ -> Just mempty
    
    -- Containers --
    ListPat _ pats -> mconcat $ map (\(L _ pat') -> pat_match pat' sa) pats -- encodes the logic that all elements of a list might be part of the pattern regardless of order
    AsPat _ (L _ bound) (L _ pat') -> -- error "At patterns (@) aren't yet supported."
      let matches = pat_match pat' sa
      in (mappend (mempty { pms_syms = singleton bound [sa] })) <$> matches -- note: `at` patterns can't be formally supported, because they might contain sub-patterns that need to hold. They also violate the invariant that "held" pattern targets have a read operation on their surface. However, since this only makes the test _less sensitive_, we'll try as hard as we can and just miss some things later.
        -- TODO test this: the outer binding and inner pattern are related: the inner pattern must succeed for the outer one to as well.
        
    -------------------------------
    -- *** MATCHING PATTERNS *** --
    -------------------------------
    _ -> fmap (\pms -> pms { -- TODO consider generic joining function
      pms_writes = pms_writes pms <> rs_writes nf_syms,
      pms_holds = pms_holds pms <> rs_holds nf_syms
    }) next_pms where
      next_pms = mconcat $ map pat_match' (rs_syms nf_syms)
      pat_match' sa' | HsVar _ v  <- unLoc $ sa_sym sa'
                    , "readMVar" == (varString $ unLoc v)
                    = Just $ mempty { -- TODO sketchy making this a "hit" when it's not yet matched
                        pms_holds = pure $ Hold {
                            h_pat = pat,
                            h_sym = sa' -- STACK good: only used to continue reduction later in `reduce`
                          }
                      }
      pat_match' sa' = case pat of
        TuplePat _ pats _ ->
          let matcher (SA _ _ _ (x:_)) = error "Argument on explicit tuple. Perhaps a tuple section, which isn't supported yet."
              matcher sa'' = case unLoc $ sa_sym sa'' of
                ExplicitTuple _ args'' _ ->
                  pat_multi_match (map unLoc pats) $ map ((\case
                      Present _ expr -> [sa'' {
                        sa_sym = expr,
                        sa_args = []
                      }] -- STACK good: this decomposition is not a function application so the stack stays the same
                      -- NOTE this is the distributivity of `consumers` onto subdata of a datatype, as well as the stack
                      -- NOTE encodes the assumption that we should preserve the original location of creation for this object, rather than this unravelling point because the datatype decompositions are trivial and can't define an object's identity
                      Missing _ -> error "Tuple sections aren't supported yet."
                    ) . unLoc) args''
                _ -> Nothing
              next_pms' = mconcat $ map matcher (rs_syms nf_syms) -- note the monoid definition of Maybe distributes the cat into ReduceSym `Just`s
          in (append_pms_writes (rs_writes nf_syms)) <$> next_pms'
          
        ConPatOut{ pat_con = L _ (RealDataCon pat_con'), pat_args = d_pat_args } -> case d_pat_args of
          PrefixCon pats ->
            let matcher sa'' | (L _ (HsConLikeOut _ (RealDataCon con)), args'') <- deapp $ sa_sym sa'' -- sym' is in NF thanks to pat_multi_match; this assumes it
                             , dataConName con == dataConName pat_con' -- TEMP disable name matching on constructor patterns, to allow symbols to always be bound to everything
                              = let flat_args = ((map (\arg'' -> [sa'' {
                                sa_sym = arg'',
                                sa_args = []
                              }]) args'') ++ sa_args sa'') -- STACK good: this decomposition is not a function application so the stack stays the same
                              -- NOTE this is the distributivity of `consumers` onto subdata of a datatype, as well as the stack
                                in pat_multi_match (map unLoc pats) flat_args
                             | otherwise = Nothing
                next_pms' = mconcat $ map matcher (rs_syms nf_syms)
            in (append_pms_writes (rs_writes nf_syms)) <$> next_pms'
        
          RecCon _ -> error "Record syntax yet to be implemented"
          
        _ -> error $ constr_ppr pat

reduce :: ReduceSyms -> ReduceSyms -- SymTable for ambient declarations
reduce syms0 =
  let expand_reads :: Writes -> SymApp -> [SymApp]
      expand_reads ws sa | HsVar _ v <- unLoc $ sa_sym sa
                         = concat $ concatMap (maybeToList . fmap (map w_sym) . (ws!?) . make_stack_key . sa_stack) $ -- a bunch of null handling
                          -- STACK good: relies on the pipe stack being correct
                          case varString $ unLoc v of -- return all pipes
                            "newMVar" -> [sa]
                            "readMVar" -> (concatMap (expand_reads ws) (head $ sa_args sa)) -- list of pipes from the first arg
                            _ -> []
                         | otherwise = [sa]
      
      -- BOOKMARK break at terminal and 
      
      -- expand_writes :: Syms a -> Writes SymApp -- BOOKMARK: ADD VISITED SET!!!
      -- -- for every pipe, make a set of terminal symbols written from different threads, updating the threads to be enemies -- this is so that we can pat-match knowing these are as terminal as we can get them; then expect pattern matching to screen out the duds (mostly unresolved functions, especially writes) -- IMPORTANT POINT: DON'T COMMIT THE OUTPUT TO MEMORY: we're going to re-expand every pipe every time
      -- expand_writes ss = M.map (concatMap ((expand_reads (rs_writes ss)) . w_sym) (rs_writes ss))
      
      expand_hold :: Writes -> Hold -> [PatMatchSyms]
      expand_hold ws h = catMaybes $ map (pat_match (h_pat h)) (expand_reads ws (h_sym h))
      
      left_outer_writes :: Writes -> Writes -> Writes
      left_outer_writes l r =
        let (l_lookups, r_lookups) = both (M.map (map (make_stack_key . sa_stack . w_sym &&& id))) (l, r) -- STACK good: used to identify unique writes; assumes `reduce` breaks cycles correctly
        in foldrWithKey (\k v m ->
            let r_lookup = r_lookups ! k
                l_lookup = l_lookups ! k
                next_writes =
                  if not $ M.member k r
                    then v
                    else concatMap (\(k', v') ->
                        concat $ maybeToList $ ([] <$ lookup k' r_lookup) <|> Just [v'] -- if it doesn't exist, add it
                      ) l_lookup
            in if not $ null next_writes
              then M.insert k next_writes m
              else m
          ) mempty l
      
      -- to_writeset :: Writes -> Set (Pipe, StackKey)
      -- to_writeset = S.fromList . concatMap (uncurry $ map . (,)) . map (second (map (stack_loc . sa_sym))) . assocs -- big assumption with `stack_loc` as the unique key for the sym
      -- from_writeset :: Set (Pipe, StackKey) -> Writes
      -- from_writeset = -- BOOKMARK: Writes -> Writes -> Writes (take the unique writes from the left side: should be more straightforward manually re: loop over all keys and find the ones that don't exist in rhs, or elems that don't exist)
      
      iterant :: ReduceStateMachine -> (Bool, ReduceStateMachine)
      iterant rs =
        let next_writes = uncurry left_outer_writes $ both rs_writes (rsm_syms rs)
            next_hold_expands = map (id &&& expand_hold next_writes) (rs_holds $ fst $ rsm_syms rs)
            next_stacks = map (\(h, pmss) -> update_head_table (unionsWith (++) $ map pms_syms pmss) (sa_stack $ h_sym h)) next_hold_expands -- STACK questionable: assumes the symbols being at the first frame is a sufficiently correct place/substitution
            -- also note that this leads to stack inconsistency, although i guess it also shows that the ReduceSym stacks aren't gospel thanks to holds
            -- NB this doesn't suffice to halt the iteration because it's still a map over a populated list; we can't avoid computation, since the stacks coming out of here will be non-empty
            make_syms w st | is_parent (st_branch st) (st_branch $ w_stack w)
                           = reduce_deep (w_sym w) -- STACK dependent: 
                           | otherwise = mempty
            -- next_syms = mconcat $ M.map (concatMap (rs_writes)) 
            
            next_syms = mconcat [
                make_syms w st |
                st <- next_stacks,
                w <- concat $ elems $ rs_writes $ fst $ rsm_syms rs
              ]
        in (
            M.null next_writes && (null $ concatMap snd next_hold_expands),
            RSM {
              rsm_stacks = next_stacks,
              rsm_syms = (next_syms, uncurry (<>) $ rsm_syms rs)
            }
          )
      res = until (fst . snd) (((+1) *** iterant . snd)) (0, (False, mempty {
        rsm_syms = (syms0, mempty)
      }))
  in snd $ rsm_syms $ snd $ snd res

reduce_deep :: SymApp -> ReduceSyms
reduce_deep sa | let args = sa_args sa
                     sym = sa_sym sa
               , length args > 0 && is_zeroth_kind sym = error $ "Application on " ++ (show $ toConstr sym)
reduce_deep sa@(SA consumers stack sym args) =
  -------------------
  -- SYM BASE CASE --
  -------------------
  let terminal = mempty { rs_syms = [sa] }
      
      unravel1 :: LHsExpr GhcTc -> [[LHsExpr GhcTc]] -> ReduceSyms -- peeling back wrappings; consider refactor to evaluate most convenient type to put here
      unravel1 target new_args =
        let nf_new_args_syms = map (map (\arg -> reduce_deep $ sa {
                sa_sym = arg,
                sa_args = []
              })) new_args
        in (mconcat $ mconcat nf_new_args_syms) {
          rs_syms = mempty
        } <> reduce_deep sa {
          -- STACK good: inherit from ambient application; if this ends up being an application, reduce_deep will update the stack accordingly
          -- CONSUMERS good: consumed law that distributes over unwrapping
          sa_sym = target,
          sa_args = map (concatMap rs_syms) nf_new_args_syms
          -- CONSUMERS good: `consumers` property at least distributes over App; if the leftmost var is of type `Consumer`, then it might make some args `consumed` as well.
        }
      
      fail = error $ "FAIL" ++ (constr_ppr $ sym)
  in case unLoc sym of
    HsLamCase _ mg -> unravel1 (HsLam NoExt mg <$ sym) []
    
    HsLam _ mg | let loc = getLoc $ mg_alts mg -- <- NB this is why the locations of MatchGroups don't matter
               , not $ is_visited (st_branch stack) sa -> -- beware about `noLoc`s showing up here: maybe instead break out the pattern matching code
                if matchGroupArity mg > length args
                  then terminal
                  else
                    let pat_matches =
                          (unLoc $ mg_alts mg) & mconcat . mconcat . map ( -- over function body alternatives
                            map ( -- over arguments
                              mconcat . catMaybes . map ( -- over possible expressions
                                uncurry (flip pat_match) -- share the same stack
                              ) . (uncurry zip) . (id *** repeat)
                            ) . zip (sa_args sa) . map unLoc . m_pats . unLoc -- `args` FINALLY USED HERE
                          ) -- NOTE no recursive pattern matching needed here because argument patterns are purely deconstructive and can't refer to the new bindings the others make
                        
                        bind_pms@(PatMatchSyms {
                            pms_syms = next_explicit_binds,
                            pms_holds = holds,
                            pms_writes = bind_writes
                          }) = grhs_binds (append_frame (AppFrame sa mempty) stack) mg -- STACK questionable: do we need the new symbol here? Shouldn't it be  -- localize binds correctly via pushing next stack location
                        next_exprs = grhs_exprs $ map (grhssGRHSs . m_grhss . unLoc) $ unLoc $ mg_alts mg
                        next_frame = AppFrame sa (union_sym_tables [pms_syms pat_matches, next_explicit_binds])
                        next_stack = append_frame next_frame stack
                        next_args = drop (matchGroupArity mg) args
                    in mempty {
                      rs_writes = pms_writes bind_pms <> pms_writes pat_matches,
                      rs_holds = pms_holds bind_pms <> pms_holds pat_matches
                    }
                      <> (mconcat $ map (\next_expr ->
                          reduce_deep sa {
                            sa_stack = next_stack,
                            sa_sym = next_expr,
                            sa_args = next_args
                          }
                        ) next_exprs) -- TODO check if the sym record update + args are correct for this stage
               | otherwise -> mempty
          
    HsVar _ (L loc v) ->
      let args' | arg1:rest <- args
                , Just "Consumer" <- varTyConName v
                  = (map (\b -> b { sa_consumers = make_stack_key stack : (sa_consumers b) }) arg1) : rest -- identify as consumer-consumed values
                   -- TODO refactor with lenses
                | otherwise = args
      in (\rs@(ReduceSyms { rs_syms }) -> -- enforce nesting rule: all invokations on consumed values are consumed
          rs {
              rs_syms = map (\sa' -> sa' { sa_consumers = sa_consumers sa' ++ consumers }) rs_syms -- TODO <- starting to question if this is doubling work
            }
        ) $
        if | v `elem` (var_ref_tail stack) ->
              -- anti-cycle var resolution
              mempty
           | varString v == "debug#" ->
              -- DEBUG SYMBOL
              mempty
           | Just left_syms <- stack_var_lookup True v stack -> -- this absolutely sucks, we have to use the "soft" search because instance name Uniques are totally unusable. Can't even use `Name`, unless I convert to string every time... which I might need to do in the future for performance reasons if I can't come up with a solution for this. 
            mconcat $ map (\sa' ->
                reduce_deep sa' {
                  sa_args = sa_args sa' ++ args', -- ARGS good: elements in the stack are already processed, so if their args are okay these ones are okay
                  sa_stack = (sa_stack sa') {
                    st_branch = mapSB ((VarRefFrame v):) (st_branch (sa_stack sa'))
                  }
                }
              ) left_syms
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
            "return" | vs:args'' <- args' -> mconcat $ map (\sa' -> reduce_deep sa' { sa_args = args'' }) vs
            -- NB about `[]` on the rightmost side of the pattern match on `args'`: it's never typesafe to apply to a monad (except `Arrow`), so if we see arguments, we have to freak out and not move forward with that.
              
            ">>" | i:o:[] <- args'
                 , let i' = map reduce_deep i
                       o' = map reduce_deep o -> -- magical monad `*>` == `>>`: take right-hand syms, merge writes
                  mconcat [i'' { rs_syms = mempty } <> o'' | i'' <- i', o'' <- o'] -- combinatorial EXPLOSION! BOOM PEW PEW
            ">>=" | i:o:[] <- args' -> -- magical monad `>>=`: shove the return value from the last stage into the next, merge writes
                  -- grabbing the writes is as easy as just adding `i` to the arguments; the argument resolution in `terminal` will take care of it
                  -- under the assumption that it's valid to assume IO is a pure wrapper, this actually just reduces to plain application of a lambda
                    mconcat $ map (\fun -> reduce_deep fun {
                          sa_args = sa_args fun ++ [i]
                        }
                      ) o
              
            "forkIO" | to_fork:[] <- args' ->
                let result = mconcat $ map (\sa' -> reduce_deep sa' {
                        sa_stack = stack {
                          st_thread = (st_branch stack, st_branch $ sa_stack sa')
                        }
                      }) to_fork
                in result {
                    rs_syms = [error "Using the ThreadID from forkIO is not yet supported."]
                  }
                  
            "putMVar" -> if length args' >= 2
              then
                let (pipes:vals:_) = args'
                in terminal {
                    rs_writes = unionWith (++) (rs_writes terminal) (unionsWith (++) [
                        singleton (make_stack_key $ sa_stack pipe) [
                            Write {
                              w_stack = stack,
                              w_sym = val
                            }
                          ]
                        | pipe <- pipes
                        , val <- vals
                      ])
                  }
              else terminal
              
            _ -> terminal
      
    HsApp _ _ _ -> -- this should only come up from the GHC AST, not from our own reduce-unwrap-wrap
      let (fun, next_args) = deapp sym
      in unravel1 fun (map pure next_args) -- I still don't remember why we special-cased HsConLikeOut to let it be `terminal` without evaluating the args, besides premature optimization  (i.e. saving the var lookup and one round of re-reducing the arguments)
      
    OpApp _ l_l l_op l_r -> unravel1 l_op [[l_l], [l_r]]
    
    -- Wrappings
    HsWrap _ _ v -> unravel1 (const v <$> sym) [] -- why is HsWrap wrapping a bare HsExpr?! No loc? Inferred from surroundings I guess (like this)
    NegApp _ v _ -> unravel1 v []
    HsPar _ v -> unravel1 v []
    SectionL _ v m_op -> unravel1 m_op [[v]]
    SectionR _ m_op v | length args > 0 -> -- need to check fo arguments because that's the only way we're going to enforce the flipping
                        let L _ (HsVar _ op) = unHsWrap m_op
                            nf_arg1_syms = reduce_deep sa { sa_sym = v, sa_args = [] }
                            arg0:args_rest = args
                        in case stack_var_lookup True (unLoc op) stack of
                          Just branch_exprs ->
                            mappend nf_arg1_syms { rs_syms = [] } $ mconcat $ map (\sa' ->
                              reduce_deep $ sa' {
                                sa_args = (sa_args sa') ++ (arg0 : (rs_syms nf_arg1_syms) : args_rest) -- TODO also do the operator constructor case
                              }
                            ) branch_exprs
                          Nothing -> terminal
                      | otherwise -> error "Unsaturated (i.e. partial) SectionR is not yet supported."
        
    HsCase _ x mg -> unravel1 (noLoc $ HsApp NoExt (HsLam NoExt mg <$ mg_alts mg) x) [] -- refactor as HsLam so we can just use that pat match code
    HsIf _ _ if_ then_ else_ -> unravel1 then_ [] <> unravel1 else_ []
    HsMultiIf ty rhss ->
      let PatMatchSyms {
              pms_syms = next_explicit_binds,
              pms_holds = holds,
              pms_writes = bind_writes
            } = grhs_binds stack rhss
          next_exprs = grhs_exprs rhss
      in mempty { rs_holds = holds, rs_writes = bind_writes }
        <> (mconcat $ map (\next_expr ->
            reduce_deep sa {
              sa_sym = next_expr,
              sa_stack = (stack { st_branch = mapSB ((AppFrame sa next_explicit_binds):) (st_branch stack) })
            }) next_exprs) -- TODO check that record update with sym (and its location) is the right move here
      
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
    
    -- SymAppinal forms
    
    HsConLikeOut _ _ -> terminal -- if length args == 0 then terminal else error "Only bare ConLike should make it to `reduce_deep`" -- still don't remember why I special-cased HsConLikeOut in HsApp
    HsOverLit _ _ -> terminal
    HsLit _ _ -> terminal
    ExplicitTuple _ _ _ -> terminal
    ExplicitSum _ _ _ _ -> terminal
    ExplicitList _ _ _ -> terminal
    -- ExplicitPArr _ _ -> terminal
    _ -> error ("Incomplete coverage of HsExpr rules: encountered " ++ (show $ toConstr $ unLoc sym))