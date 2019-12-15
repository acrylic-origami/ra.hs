{-# LANGUAGE Rank2Types, NamedFieldPuns, LambdaCase, TupleSections, MultiWayIf, DeriveDataTypeable #-}
module Ra (
  or_pat_match_many,
  and_pat_match_many,
  pat_match,
  reduce_deep
) where

import GHC
import HsExtension ( XOverLit(..) )
import DataCon ( dataConName, dataConRepType )
import ConLike ( ConLike (..) )
import Type ( splitAppTy_maybe, splitTyConApp_maybe, dropForAlls, splitFunTys )
import Name ( mkSystemName, nameOccName )
import OccName ( mkVarOcc, occNameString )
import Unique ( mkVarOccUnique )
import FastString ( mkFastString ) -- for WildPat synthesis
import SrcLoc ( noSrcSpan )
import Var ( mkLocalVar, varType, setVarType ) -- for WildPat synthesis
import IdInfo ( vanillaIdInfo, IdDetails(VanillaId) ) -- for WildPat synthesis

import Data.List ( elemIndex )
import Data.Bool ( bool )
import Data.Coerce ( coerce )
import Data.Char ( isLower )
import Data.Tuple ( swap )
import Control.Arrow ( first, second, (***), (&&&) )
import Data.Function ( (&) )
import Data.Maybe ( catMaybes, fromMaybe, maybeToList, isNothing )
import Data.Data ( toConstr, Data(..), Typeable(..) )
import Data.Generics ( everywhere, everywhereBut, GenericT(), everything, everythingBut, GenericQ(), mkQ, mkT, extQ, extT )
import Data.Generics.Extra ( constr_ppr, GenericQT, gmapQT, everywhereWithContextLazyBut, everywhereWithContextBut, extQT, mkQT )
import Data.Semigroup ( (<>) )
import Data.Monoid ( mempty, mconcat )
import Control.Monad ( join, guard, foldM )
import Control.Applicative ( (<|>), liftA2 )
import Control.Exception ( assert )

import Data.Tree ( levels )
import Data.Graph.Inductive.PatriciaTree ( Gr(..) )
import Data.Graph.Inductive.Query.DFS ( dff )
import Data.Graph.Inductive.NodeMap ( mkMapGraph, mkNodes )

import Data.Map.Strict ( Map(..), unionsWith, unions, unionWith, union, singleton, (!?), (!), foldlWithKey, foldrWithKey, keys, mapWithKey, assocs)
import qualified Data.Map.Strict as M ( null, member, empty, insert, map, elems )
import Data.Set ( Set(..), intersection, difference, (\\) )
import qualified Data.Set as S ( fromList, member, insert, size )
-- import qualified Data.Set as S ( insert )

import qualified Ra.Refs as Refs
import Ra.GHC.Translate
import Ra.GHC.Util
import Ra.Lang
import Ra.Extra
import Ra.Lang.Extra
import Ra.Refs ( write_funs, read_funs )

pat_match_one ::
  LPat GhcTc
  -> SymApp
  -> Maybe LUT
pat_match_one pat sa =
  case unLoc pat of
    ---------------------------------
    -- +++ UNWRAPPING PATTERNS +++ --
    ---------------------------------
    WildPat ty -> Just mempty -- TODO check if this is the right [write, haha] behavior
      
    -- Wrappers --
    LazyPat _ pat' -> pat_match_one pat' sa
    ParPat _ pat' -> pat_match_one pat' sa
    BangPat _ pat' -> pat_match_one pat' sa
    -- SigPatOut (L _ pat) _ -> pat_match_one pat sa
    
    -- Bases --
    VarPat _ (L _ v) -> Just $ singleton v [sa]
    LitPat _ _ -> Just mempty -- no new name bindings
    NPat _ _ _ _ -> Just mempty
    
    -- Containers --
    ListPat _ pats -> undefined -- need to use pat_match_zip
    -- ListPat _ pats -> unionsWith (++) $ map (\(L _ pat') -> pat_match_one pat' sa) pats -- encodes the logic that all elements of a list might be part of the pattern regardless of order
    AsPat _ (L _ bound) pat' -> -- error "At patterns (@) aren't yet supported."
      let matches = pat_match_one pat' sa
      in (unionWith (++) $ singleton bound [sa]) <$> matches -- note: `at` patterns can't be formally supported, because they might contain sub-patterns that need to hold. They also violate the invariant that "held" pattern targets have a read operation on their surface. However, since this only makes the test _less sensitive_, we'll try as hard as we can and just miss some things later.
        -- TODO test this: the outer binding and inner pattern are related: the inner pattern must succeed for the outer one to as well.
        
    -------------------------------
    -- +++ MATCHING PATTERNS +++ --
    -------------------------------
    TuplePat _ pats _ | TupleConstr _ <- sa_sym sa -> and_pat_match_many (zip pats (sa_args sa))
                      | otherwise -> mempty -- error $ "Argument on explicit tuple. Perhaps a tuple section, which isn't supported yet. PPR:\n" ++ (ppr_sa ppr_unsafe sa)
                      
    ConPatOut { pat_con, pat_args = d_pat_args } -> case unLoc pat_con of
      RealDataCon pat_con' -> case d_pat_args of
        PrefixCon pats | (Sym sym) <- sa_sym sa
                       , (L _ (HsConLikeOut _ (RealDataCon con)), args'') <- deapp sym
                       , dataConName con == dataConName pat_con' -- TEMP disable name matching on constructor patterns, to allow symbols to always be bound to everything
                       -> let flat_args = ((map (\arg'' -> [sa {
                          sa_sym = Sym arg'',
                          sa_args = []
                        }]) args'') ++ sa_args sa) -- STACK good: this decomposition is not a function application so the stack stays the same
                            -- NOTE this is the distributivity of `consumers` onto subdata of a datatype, as well as the stack
                              in and_pat_match_many (zip pats flat_args)
                       | otherwise -> Nothing
      
        InfixCon l r -> if ":" == (occNameString $ nameOccName $ dataConName pat_con')
          then case sa_sym sa of -- TODO URGENT test this -- special-case list decomp because lists have their own constr syntax
            ListConstr _ -> if length (sa_args sa) > 0
              then (or_pat_match_many (zip (repeat l) (sa_args sa))) <> (pat_match_one r sa) -- `or` here because any member of the list can work -- `union` mechanics are fine here because the bound names can't be shared between head and tail
              else Nothing
            _ -> Nothing
          else pat_match_one
            ((\pat' -> pat' {
                pat_args = PrefixCon [l, r]
              }) <$> pat)
            sa
        RecCon _ -> error "Record syntax yet to be implemented"
        _ -> error $ show (getLoc pat_con) ++ "\n" ++ constr_ppr d_pat_args
      _ -> error $ constr_ppr pat
      
    _ -> error $ constr_ppr pat

or_pat_match_many :: [Bind] -> Maybe LUT
or_pat_match_many = pat_match_many (\a b -> liftA2 (unionWith (++)) a b <|> a <|> b) -- could've been `<>` if that was `unionWith (++)` for these maps, but instead `union` destroys the rhs in collisions

and_pat_match_many :: [Bind] -> Maybe LUT
and_pat_match_many = pat_match_many (liftA2 (unionWith (++)))

pat_match_many :: (Maybe LUT -> Maybe LUT -> Maybe LUT) -> [Bind] -> Maybe LUT
pat_match_many f = foldr1 f . map mapper
  where mapper (pat, exprs@(_:_)) = foldr1 f $ map (pat_match_one pat) exprs
        mapper _ = Nothing -- TODO being a little sloppy here, assuming that `Nothing` is an acceptable result for a default. In fact, note that if `f` was `const (const (Just mempty))` this would still return `Nothing` if there are single matches. Then there's a sharp phase change with 2 elems when they all pass. 

sub :: Map Id [SymApp] -> SymApp -> Maybe ReduceSyms
sub t sa = -- assumes incoming term is a normal form
  let subbed_sa = sub_sa_types_wo_stack sa sa -- really hope this works
  in case sa_sym subbed_sa of
    Sym (L loc s@(HsVar _ (L _ v))) -> (
          mconcat
          -- . map (\rs' ->
          --     let rss' = map (sub t) (rs_syms rs')
          --     in map (uncurry (id )) (zip rss' (rs_syms rs')))
          . map (\sa' -> reduce_deep sa' {
                sa_args = (sa_args sa') <> (sa_args subbed_sa)
              })
        )
      <$> (snd $ (sa, t !? v)) -- DEBUG
    _ -> Nothing

pat_match :: [Bind] -> PatMatchSyms
pat_match binds = 
  let dig :: LUT -> GenericQT [DoStmt]
      dig table = dig' 0 where
        dig' :: Int -> GenericQT [DoStmt]
        dig' n | n < max_iter -- dig' nominally takes either [SymApp] (interally) or PatMatchSyms (externally)
               = go True where
                go :: Bool -> GenericQT [DoStmt]
                go is_first = first mconcat . ( -- not in love with outer mconcat but it's more common among the queries than it is uncommon
                    gmapQT (go is_first)
                    `mkQT` (
                        second concat
                        . unzip . map (\sa ->
                            second (map (\sa' ->
                              (
                                  if sa_is_monadic sa
                                    then reloc sa' sa
                                    else sa'
                                ) {
                                  sa_is_monadic = snd (sa', sa_is_monadic sa)
                                }
                            )) $ (
                              if | Just next_rs <- sub table sa
                                 , (next_stmts, next_sas) <- dig' (n + 1) (rs_syms next_rs)
                                 -> (rs_stmts next_rs <> next_stmts, next_sas)
                                 | otherwise
                                 -> (mconcat *** pure) $ gmapQT (go False) sa
                              )
                          )
                      )
                    `extQT` ((mempty,) :: Stack -> ([[DoStmt]], Stack))
                  )
        dig' _ = (mempty,)
        
      (rs0, binds0) = first mconcat $ unzip $ map ((\(pat, rs) -> (rs, (pat, rs_syms rs))) . second (mconcat . map reduce_deep)) binds -- don't assume any SymApp Syms coming in are NF
      pms0 = PatMatchSyms {
        pms_stmts = rs_stmts rs0,
        pms_syms = mempty {
          stbl_binds = binds0
        }
      }
      
      max_iter :: Int
      max_iter =
        let get_ids :: GenericQ [Id]
            get_ids = everythingBut (<>) (
              ([], False)
              `mkQ` ((,False) . pure :: Id -> ([Id], Bool))
              `extQ` (const ([], True) :: Stack -> ([Id], Bool)))
            -- in S.size $ S.fromList (get_ids binds0) -- fallback: much simpler, slightly looser bound than graph traversal, probably more robust
            
            (patvars, expvars) = mconcat $ map (get_ids *** get_ids) binds0
            expvars' = filter (`elem` patvars) expvars
            
            flat_binds = [
                (patvar, expvar, ())
                  | patvar <- patvars
                  , expvar <- expvars'
              ]
            nodes = map (\(x,_,_) -> x) flat_binds
            gr :: Gr Id ()
            (gr, nodemap) = mkMapGraph nodes flat_binds
        in (+1) $ foldl max 0 $ map (length . levels) $ dff (map fst $ fst $ mkNodes nodemap nodes) gr
        
      (stmtsn, pmsn) = dig (fromMaybe mempty $ or_pat_match_many binds0) pms0
      
      tie_to_table :: Data d => d -> d
      tie_to_table = mkT (\sa -> sa {
          sa_stack = ((BindFrame next_table):) (sa_stack sa)
        })
      
      next_map = if length (stbl_binds $ pms_syms pmsn) > 0
        then fromMaybe mempty (or_pat_match_many (stbl_binds $ pms_syms pmsn)) -- `or` here because scattered bindings
        else mempty
        
      next_table = snd $
        ((next_map, binds), everywhereBut
          (False `mkQ` (const True :: Stack -> Bool))
          (tie_to_table
            `extT` filter (\x -> isNothing $ sub next_map x))
          (pms_syms pmsn) {
            stbl_table = if length (stbl_binds next_table) > 0
              then fromMaybe mempty (or_pat_match_many (stbl_binds next_table)) -- `or` here because scattered bindings
              else mempty
          }) -- TODO this is pretty ugly, find a better way to avoid twice the work
  in (everywhereBut
      (False `mkQ` (const True :: Stack -> Bool))
      tie_to_table
      (pmsn { pms_syms = mempty })
    ) {
    pms_syms = next_table 
  }

-- app_types :: Type -> Type -> Type
-- app_types l r = uncurry mkFunTys $ first (update_head (const r)) $ splitFunTys l

reduce_deep :: SymApp -> ReduceSyms
reduce_deep sa | let args = sa_args sa
                     sym = sa_sym sa
               , length args > 0 && is_zeroth_kind sym = error $ "Application on " ++ (show $ toConstr sym)
reduce_deep sa@(SA consumers is_monadic locstack stack m_sym args thread) =
  -------------------
  -- SYM BASE CASE --
  -------------------
  let terminal = mempty { rs_syms = [ sa ] }
      
      unravel1 :: LHsExpr GhcTc -> [[LHsExpr GhcTc]] -> ReduceSyms -- peeling back wrappings; consider refactor to evaluate most convenient type to put here
      unravel1 target new_args =
        let nf_new_args_syms = map (map (\arg -> reduce_deep $ sa {
                sa_sym = Sym arg,
                sa_is_monadic = False, -- LAW args aren't monadic
                sa_args = []
              })) new_args
        in (mconcat $ mconcat nf_new_args_syms) {
          rs_syms = mempty
        } <> reduce_deep sa {
          -- STACK good: inherit from ambient application; if this ends up being an application, reduce_deep will update the stack accordingly
          -- CONSUMERS good: consumed law that distributes over unwrapping
          sa_sym = Sym target,
          sa_args = (map (concatMap rs_syms) nf_new_args_syms) <> (sa_args sa)
          -- CONSUMERS good: `consumers` property at least distributes over App; if the leftmost var is of type `Consumer`, then it might make some args `consumed` as well.
        }
      
      fail = error $ "FAIL" ++ (constr_ppr $ m_sym)
  in case m_sym of
    Sym sym -> case unLoc sym of
      -------------------------------
      -- +++ NON-TRIVIAL EXPRS +++ --
      -------------------------------
      
      HsLamCase _ mg -> unravel1 (HsLam NoExt mg <$ sym) []
      
      HsLam _ mg | is_visited stack sa -> mempty
                 | matchGroupArity mg <= length args 
                 , let next_arg_binds = concatMap ( flip zip (sa_args sa) . m_pats . unLoc ) (unLoc $ mg_alts mg)
                 , Just next_arg_matches <- if length next_arg_binds > 0
                    then and_pat_match_many next_arg_binds -- `and` here because we need to stop evaluating if this alternative doesn't match the input
                    else Just mempty -- NOTE no recursive pattern matching needed here because argument patterns are purely deconstructive and can't refer to the new bindings the others make
                 -> let next_af = AppFrame sa (SymTable {
                            stbl_table = next_arg_matches,
                            stbl_binds = next_arg_binds
                          })
                        next_exprs = everywhereBut (False `mkQ` (const True :: Stack -> Bool)) (sub_sa_types_T sa) -- TODO URGENT check if removing the Var special case and letting `sub_sa_types_T` handle it here was the right thing to do
                          $ grhs_exprs $ map (grhssGRHSs . m_grhss . unLoc) $ unLoc $ mg_alts mg -- TEMP
                        bind_pms = pat_match $ map (second (map (\sa' -> sa' {
                            sa_stack = sa_stack sa' ++ (next_af : stack),
                            sa_loc = sa_loc sa' ++ (next_af : locstack)
                          }))) $ (grhs_binds True) mg -- STACK questionable: do we need the new symbol here? Shouldn't it be  -- localize binds correctly via pushing next stack location
                        next_frames = [BindFrame (pms_syms bind_pms), next_af]
                        next_stack = (next_frames++) stack
                        next_loc = (next_frames++) locstack
                        next_args = drop (matchGroupArity mg) args
                    in mempty {
                      rs_stmts = pms_stmts bind_pms
                    }
                      <> (mconcat $ map (\next_expr ->
                          reduce_deep sa {
                            sa_loc = next_loc,
                            sa_stack = next_stack,
                            sa_sym = Sym next_expr,
                            sa_args = next_args
                          }
                        ) next_exprs) -- TODO check if the sym record update + args are correct for this stage
                 | otherwise -> terminal
            
      HsVar _ (L _ v) ->
        let args' | arg1:rest <- args
                  , Just "Consumer" <- varTyConName v
                    = (map (\b -> b { sa_consumers = make_loc_key sa : (sa_consumers b) }) arg1) : rest -- identify as consumer-consumed values
                     -- TODO refactor with lenses
                  | otherwise = args
            terminal' = mempty { rs_syms = [sa { sa_args = args' }] }
              
        in (\rs@(ReduceSyms { rs_syms }) -> -- enforce nesting rule: all invokations on consumed values are consumed
            rs {
                rs_syms = map (\sa' -> sa' { sa_consumers = sa_consumers sa' ++ consumers }) rs_syms -- TODO <- starting to question if this is doubling work
              }
          ) $
          if | varString v == "debug#" ->
                -- DEBUG SYMBOL
                mempty
             | Just left_syms <- stack `stack_var_lookup` v ->
              mconcat $ map (\sa' ->
                  let next_rs = reduce_deep sa' {
                          sa_args = sa_args sa' <> args', -- ARGS good: elements in the stack are already processed, so if their args are okay these ones are okay
                          sa_stack = (sa_stack sa') <> stack
                        }
                  in next_rs {
                      rs_syms = map (\sa' ->
                          (
                              if is_monadic
                                then reloc sa' sa
                                else sa'
                            ) {
                              sa_is_monadic = is_monadic
                            }
                        ) (rs_syms next_rs)
                    }
                ) left_syms
             | otherwise ->
              ------------------------------------
              -- +++ SPECIAL CASE FUNCTIONS +++ --
              ------------------------------------
              
              -------------------------------------
              -- +++ IO-like monad behaviors +++ --
              -------------------------------------
              let _ap f v =
                    let next_rs = mconcat $ map (\fun -> reduce_deep fun {
                            sa_args = sa_args fun ++ [v]
                          }) f
                        next_syms = map (\sa -> sa { sa_is_monadic = True }) (rs_syms next_rs)
                    in next_rs {
                      rs_syms = next_syms,
                      rs_stmts = rs_stmts next_rs <> next_syms <> v -- TODO including both inputs and outputs in the worst-case will duplicate most statements (e.g. if it's a long chain of `>>` and `>>=`), which ends up polluting the top-level, maybe with an exponential number of terms. However, the base case is non-trivial because if it's just this statement alone, we would need to log both as statements for proper coverage.
                    }
                  
              in if | varString v `elem` [ "error" ] -> mempty
                    | varString v `elem` [
                       "returnIO",
                       "returnSTM",
                       "unSTM",
                       "unsafeIOToSTM",
                       "atomically",
                       "stToIO",
                       "coerce" -- interesting
                     ]
                      || (varString v == "return"
                          && fromMaybe False (
                              do
                                (app_con, _) <- splitAppTy_maybe $ snd $ splitFunTys $ strip_contexts_deep $ everywhere (mkT dropForAlls) $ varType v
                                (ty_con, _) <- splitTyConApp_maybe app_con
                                return $ (occNameString $ getOccName ty_con) == "ST"
                            )
                        )
                    , vs:args'' <- args'
                    -> mconcat $ map (\sa' -> reduce_deep $ sa' { sa_args = ((sa_args sa') <> args'') }) vs
                    | varString v `elem` [
                       -- ">>",
                       "thenIO",
                       "thenSTM"
                     ]
                    , i:o:[] <- args'
                    , let reduce' = map ((\rs -> rs { rs_syms = map (\sa' -> sa' { sa_is_monadic = True }) (rs_syms rs) }) . reduce_deep)
                          i' = reduce' i
                          o' = reduce' o
                          next_rs = mconcat [i'' { rs_syms = mempty } <> o'' | i'' <- i', o'' <- o']-- combinatorial EXPLOSION! BOOM PEW PEW -- magical monad `*>` == `>>`: take right-hand syms, merge writes
                    -> next_rs {
                        rs_stmts = rs_stmts next_rs <> rs_syms next_rs <> rs_syms (mconcat i')
                     }
                       
                    | varString v `elem` [
                       -- ">>=",
                       "bindSTM",
                       "bindIO"
                     ]
                    , v:f:[] <- args'
                    -> _ap f v
                     -- magical monad `>>=`: shove the return value from the last stage into the next, merge writes
                     -- grabbing the writes is as easy as just adding `i` to the arguments; the argument resolution in `terminal` will take care of it
                     -- under the assumption that it's valid to assume IO is a pure wrapper, this actually just reduces to plain application of a lambda
                    
                    | varString v `elem` [
                        -- "<*>",
                        "ap",
                        "<$>"
                        -- "fmap" -- TEMP
                      ]
                    , f:v:[] <- args'
                    -> _ap f v
                   
                    | varString v == "forkIO"
                    , to_fork:[] <- args'
                    ->
                     let result = mconcat $ map (everywhereBut (False `mkQ` (const True :: Stack -> Bool)) (mkT $ \sa' -> sa' { sa_thread = Just sa }) . reduce_deep) to_fork
                     in result {
                         rs_syms = [error "Using the ThreadID from forkIO is not yet supported."]
                       }
                       
                    | varString v `elem` [
                       "retry",
                       "throwSTM"
                     ] -> mempty
                   
                    | otherwise -> terminal'
        
      HsApp _ _ _ -> -- this should only come up from the GHC AST, not from our own reduce-unwrap-wrap
        let (fun, next_args) = deapp sym
        in unravel1 fun (map pure next_args) -- I still don't remember why we special-cased HsConLikeOut to let it be `terminal` without evaluating the args, besides premature optimization  (i.e. saving the var lookup and one round of re-reducing the arguments)
      
      -----------------------
      -- +++ WRAPPINGS +++ --
      -----------------------
      
      OpApp _ l_l l_op l_r -> unravel1 l_op [[l_l], [l_r]]
      HsWrap _ _ _ -> unravel1 (unHsWrap sym) []
      ExprWithTySig _ v -> unravel1 v []
      HsAppType _ v -> unravel1 v []
      NegApp _ v _ -> unravel1 v []
      HsPar _ v -> unravel1 v []
      SectionL _ v m_op -> unravel1 m_op [[v]]
      SectionR _ m_op v | length args > 0 -> -- need to check fo arguments because that's the only way we're going to enforce the flipping
                          let L _ (HsVar _ (L _ op)) = unHsWrap m_op
                              nf_arg1_syms = reduce_deep sa { sa_sym = Sym v, sa_args = [] }
                              arg0:args_rest = args
                          in case stack `stack_var_lookup` op of
                            Just stack_exprs ->
                              mappend nf_arg1_syms { rs_syms = [] } $ mconcat $ map (\sa' ->
                                reduce_deep $ sa' {
                                  sa_args = (sa_args sa') ++ (arg0 : (rs_syms nf_arg1_syms) : args_rest) -- TODO also do the operator constructor case
                                }
                              ) stack_exprs
                            Nothing -> terminal
                        | otherwise -> terminal -- error ("Unsaturated (i.e. partial) SectionR is not yet supported, at:\n  " ++ (show $ getLoc sym)) -- softening the error a bit, but this is still invalid
          
      HsCase _ x mg -> unravel1 (noLoc $ HsApp NoExt (HsLam NoExt mg <$ mg_alts mg) x) [] -- refactor as HsLam so we can just use that pat match code
      HsIf _ _ if_ then_ else_ -> unravel1 then_ [] <> unravel1 else_ []
      HsMultiIf ty rhss ->
        let PatMatchSyms {
                pms_syms = next_explicit_binds,
                pms_stmts = bind_stmts
              } = pat_match $ (grhs_binds True) rhss
            next_exprs = grhs_exprs rhss
            next_frame = AppFrame sa next_explicit_binds
        in mempty { rs_stmts = bind_stmts }
          <> (mconcat $ map (\next_expr ->
              reduce_deep sa {
                sa_sym = Sym next_expr,
                sa_stack = (next_frame:) stack,
                sa_loc = (next_frame:) locstack
              }) next_exprs) -- TODO check that record update with sym (and its location) is the right move here
        
      HsLet _ _ expr -> unravel1 expr [] -- assume local bindings already caught by surrounding function body (HsLam case)
      HsDo _ _ (L _ stmts) -> foldl (\syms (L _ stmt) ->
          let m_next_expr :: Maybe (LHsExpr GhcTc) -- Quite inflexible type: the stuff going on there doesn't let you do much
              m_next_expr = case stmt of
                LastStmt _ expr _ _ -> Just expr -- kill the results from all previous stmts because of the semantics of `>>`
                -- ApplicativeStmt _ _ _ -> undefined -- TODO yet to appear in the wild and be implemented
                BindStmt _ _pat expr _ _ty -> Just expr
                LetStmt _ _ -> Nothing
                BodyStmt _ expr _ _ -> Just expr
                ParStmt _ _ _ _ -> Nothing -- not analyzed for now, because the list comp is too niche (only used for parallel monad comprehensions; see <https://gitlab.haskell.org/ghc/ghc/wikis/monad-comprehensions>)
                _ -> fail
                -- fun fact: I thought ParStmt was for "parenthesized", but it's "parallel"
              m_next_syms = (reduce_deep . (\expr -> sa { sa_sym = Sym expr, sa_is_monadic = True })) <$> m_next_expr
          in syms { -- combining rule assumes LastStmt is really the last statement every time
            rs_syms = fromMaybe mempty (rs_syms <$> m_next_syms),
            rs_stmts = rs_stmts syms <> fromMaybe mempty ((rs_stmts <$> m_next_syms) <> (rs_syms <$> m_next_syms))
          }
        ) mempty stmts -- push all the work to another round of `reduce_deep`.
      
      ----------------------------
      -- +++ TERMINAL FORMS +++ --
      ----------------------------
      
      HsConLikeOut _ _ -> terminal -- if length args == 0 then terminal else error "Only bare ConLike should make it to `reduce_deep`" -- still don't remember why I special-cased HsConLikeOut in HsApp
      HsOverLit _ _ -> terminal
      HsLit _ _ -> terminal
      ExplicitTuple _ args _ ->
        let (next_rs, args') = first mconcat $ unzip $ map (\case
                L _ (Present _ s) -> (id &&& rs_syms) $ reduce_deep $ sa {
                    sa_sym = Sym s,
                    sa_args = []
                  }
                _ -> error "Tuple sections not yet supported"
              ) args
        in next_rs { rs_syms = mempty } <> (reduce_deep $ sa {
          sa_sym = TupleConstr (getLoc sym),
          sa_args = args'
        })
      -- ExplicitSum _ _ _ _ -> terminal
      ExplicitList _ _ args ->
        let (next_rs, args') = first mconcat $ unzip $ map (\s ->
                (id &&& rs_syms) $ reduce_deep $ sa {
                  sa_sym = Sym s,
                  sa_args = []
                }
              ) args
        in next_rs { rs_syms = mempty } <> (reduce_deep $ sa {
          sa_sym = ListConstr (getLoc sym),
          sa_args = args'
        })
      ExplicitList _ (Just _) _ -> error "List comprehensions not yet supported"
      -- ExplicitPArr _ _ -> terminal
      _ -> error ("Incomplete coverage of HsExpr rules: encountered " ++ (show $ toConstr $ unLoc sym))
    _ -> terminal