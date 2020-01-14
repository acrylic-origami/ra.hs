{-# LANGUAGE TupleSections, LambdaCase, Rank2Types #-}
module Ra.Plugin.CallGraph where
-- SYB for top-level binds
-- SYB for HsVar
-- SYB for HsApp
-- match against type and name in top-level
-- graph

import GHC
import Var ( Id, Var(..), varType, varName )
import Name ( nameOccName )
import OccName ( occNameString )

import Data.Generics ( Data(..), everything, mkQ, GenericQ, listify )
import Control.Arrow ( (&&&), (***), first, second )
import Data.Maybe
import Data.Graph.Inductive.Query.DFS ( condensation, reachable )
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree

import Ra.Impure ( reduce )
import Ra.Lang ( SymApp(..), Bind(..), ReduceSyms(..), SymTable(..), Sym(..), StackFrame(..), sa_from_sym )
import Ra.GHC.Util ( inst_subty )
import Ra ( or_pat_match_many )

import Debug.Trace ( trace )

import Paths_rahse ( getDataFileName )

mk_call_graph :: [Bind] -> Gr Bind ()
mk_call_graph tl_binds =
  let tl_binds' = second (map (map sa_sym)) $ unzip tl_binds -- ([LPat], [[HsExpr]])
      -- not quite accurate because we haven't subbed from HsWrap yet, but good 1st order
      -- tl_vars :: [[Id]]
      q :: GenericQ [Id]
      q = everything (++) (mempty `mkQ` ((\case { HsVar _ n -> [unLoc n]; _ -> mempty }) :: HsExpr GhcTc -> [Id]))
      (tl_vars, inner_vars) = (map (listify (False `mkQ` (const True :: Id -> Bool))) *** map q) $ tl_binds'
      edges = 
        concatMap (uncurry (map . (,,())))
        $ zip [0..] $ [
            catMaybes $ [
                if ((occNameString $ nameOccName $ varName tl) == (occNameString $ nameOccName $ varName inner)) && (isJust $ inst_subty (varType tl) (varType inner))
                  then Just tl_idx
                  else Nothing
                | (tl_idx, tls) <- zip [0..] tl_vars, tl <- tls, inner <- inners
              ]
            | inners <- inner_vars
          ]
    in mkGraph (zip [0..] tl_binds) edges

top_binds :: [Bind] -> [Bind]
top_binds binds0 =
  let gr = mk_call_graph binds0
      cgr = condensation gr
  in concatMap (map (fromJust . (lab gr)) . snd)
    $ filter (
        uncurry (&&) . (
            (==0) . length . pre cgr
            &&& (>0) . length . suc cgr
          ) . fst
      )
    $ labNodes cgr

reduce_all :: [Bind] -> [ReduceSyms]
reduce_all =
  map (\top ->
    fst $ until
      (all (<=0) . snd)
      (\(rs, n) ->
          trace (show n) $
          first reduce $ unzip $ map (\sa ->
              let n_filler_args =
                    (\case { Sym (L _ (HsLam _ mg)) -> matchGroupArity mg; _ -> 0 })
                    $ sa_sym sa
                  delta_args = n_filler_args - (length $ sa_args sa)
              in (
                  sa {
                    sa_args = sa_args sa ++ replicate delta_args [sa_from_sym EntryPoint]
                  },
                  delta_args
                )
            ) (rs_syms rs)
        )
      (ReduceSyms {
          rs_syms = snd top,
          rs_stmts = mempty
        }, [1])
  )
  . top_binds