module Ra.Lang.Extra (
  ppr_sa
) where

import Data.Tuple.Extra ( (&&&) )
import Ra.Lang ( SymApp(..), Sym(..) )
import Outputable ( showPpr )

ppr_sa dflags = go 0 where
  go n = 
    let indent = (replicate n ' ')
    in  (++(indent ++ ">"))
         . (
          (indent ++ "<")++)
          . uncurry (++)
          . (
              (showPpr dflags . expr . sa_sym)
              &&& concatMap (
                  (++("\n" ++ indent ++ " ]\n"))
                  . (("\n" ++ indent ++ " [\n")++)
                  . concatMap (go (n+1))
                ) . sa_args
            )