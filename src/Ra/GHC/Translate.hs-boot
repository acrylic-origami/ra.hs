{-# LANGUAGE Rank2Types #-}
module Ra.GHC.Translate (
  grhs_binds,
  bind_to_table,
) where

import GHC
import Data.Generics

import Ra.Lang ( Sym, Stack, SymTable, PatMatchSyms, Bind )
import Ra.Extra

bind_to_table :: HsBind GhcTc -> [Bind]
grhs_binds :: GenericQ [Bind]