{-# LANGUAGE Rank2Types #-}

module Ra.Lang.Extra (
  ppr_sa,
  ppr_rs,
  ppr_pms,
  ppr_stack
) where

import GHC ( LHsExpr, GhcTc )
import Data.Bool ( bool )
import Data.Tuple.Extra ( (&&&), (***) )

import Ra.Lang ( SymApp(..), Sym(..), unSB, Stack(..), ReduceSyms(..), PatMatchSyms(..), Hold(..), Write(..), Writes )

import Outputable ( Outputable(..), showPpr )
import Data.Map.Strict ( assocs )
import qualified Data.Map.Strict as M ( map, elems, assocs )

type Printer = (forall o. Outputable o => o -> String)

ppr_sa :: Printer -> SymApp -> String
ppr_sa show' = go 0 where
  go n = 
    let indent = (replicate n ' ')
    in  (++(indent ++ ">"))
         . (
          uncurry (++)
          . (
              uncurry (++) . (
                  bool "" "*" . not . null . sa_consumers
                  &&& ((indent ++ "<")++) . (show' . sa_sym)
                )
              &&& concatMap (
                  (++("\n" ++ indent ++ " ]\n"))
                  . (("\n" ++ indent ++ " [\n")++)
                  . concatMap (go (n+1))
                ) . sa_args
            )
          )

ppr_writes :: Printer -> Writes -> String
ppr_writes show' = concatMap ((++"\n---\n") . uncurry ((++) . (++" -> ")) . (show' *** concatMap ((++"\n") . ppr_sa show' . w_sym))) . assocs

ppr_hold :: Printer -> Hold -> String
ppr_hold show' = uncurry ((++) . (++" <- ")) . (show' . h_pat &&& ppr_sa show' . h_sym)

ppr_rs :: Printer -> ReduceSyms -> String
ppr_rs show' = flip concatMap printers . (("\n===\n"++).) . flip ($) where
  printers = [
      concatMap ((++"\n") . ppr_sa show') . rs_syms
      , ppr_writes show' . rs_writes
      , concatMap ((++"\n---\n") . ppr_hold show') . rs_holds
    ]

ppr_pms :: Printer -> PatMatchSyms -> String
ppr_pms show' = flip concatMap printers . (("\n===\n"++).) . flip ($) where
  printers = [
      concatMap ((++"\n") . uncurry ((++) . (++" -> ")) . (show' *** concatMap ((++"\n") . ppr_sa show'))) . assocs . pms_syms
      , ppr_writes show' . pms_writes
      , concatMap ((++"\n---\n") . ppr_hold show') . pms_holds
    ]

ppr_stack :: Printer -> Stack -> String
ppr_stack show' = show . map (map (uncurry (++) . ((++"->") . show' *** concatMap (ppr_sa show'))) . M.assocs . snd) . unSB . st_branch