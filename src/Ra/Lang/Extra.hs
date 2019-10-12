{-# LANGUAGE Rank2Types #-}

module Ra.Lang.Extra (
  ppr_sa,
  ppr_stack
) where

import GHC ( LHsExpr, GhcTc )
import Data.Bool ( bool )
import Data.Tuple.Extra ( (&&&), (***) )
import Ra.Lang ( SymApp(..), Sym(..), unSB, Stack(..) )
import Outputable ( Outputable(..), showPpr )
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
                  &&& ((indent ++ "<")++) . (show' . expr . sa_sym)
                )
              &&& concatMap (
                  (++("\n" ++ indent ++ " ]\n"))
                  . (("\n" ++ indent ++ " [\n")++)
                  . concatMap (go (n+1))
                ) . sa_args
            )
          )

ppr_stack :: Printer -> Stack -> String
ppr_stack show' = show . map (map (uncurry (++) . ((++"->") . show' *** concatMap (ppr_sa show'))) . M.assocs . snd) . unSB . st_branch