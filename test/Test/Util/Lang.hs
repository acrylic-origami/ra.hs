module Test.Util.Lang (
  str_syms,
  tSA
) where

import Data.Generics ( extT, extQ, mkT, mkQ, everything, everywhere, gmapQ, gmapT, Data(..), GenericQ, GenericT )

import Ra.Lang
import Ra.Lang.Extra

str_syms :: GenericQ [SymApp String]
str_syms = concat . (gmapQ str_syms
    `extQ` (pure . pure . stringify :: SymApp Sym -> [[SymApp String]])
    `extQ` (const mempty :: Stack -> [[SymApp String]])
  ) where
  stringify sa = sa {
      sa_sym = ppr_unsafe (sa_sym sa :: Sym),
      sa_args = map (concatMap str_syms) (sa_args sa :: [[SymApp Sym]]),
      sa_thread = (head . str_syms) <$> (sa_thread sa)
    }

tSA :: s -> [[SymApp s]] -> SymApp s
tSA sym args = (sa_from_sym sym) {
    sa_args = args
  }