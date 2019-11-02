{-# LANGUAGE Rank2Types #-}
module Ra.GHC (
  unHsWrap,
  deapp,
  grhs_exprs,
  grhs_binds,
  bind_to_table,
  mg_drop,
  mg_flip,
  varString,
  varTyConName
) where

import GHC
import Data.Generics

import Ra.Lang ( Sym, Stack, SymTable, PatMatchSyms, Bind )
import Ra.Extra

unHsWrap :: LHsExpr GhcTc -> LHsExpr GhcTc -- almost don't have to export this, except for legit use case for unwrapping `OpApp`s
deapp :: LHsExpr GhcTc -> (LHsExpr GhcTc, [LHsExpr GhcTc])
bind_to_table :: HsBind GhcTc -> [Bind]
grhs_exprs :: GenericQ [LHsExpr GhcTc]
grhs_binds :: GenericQ [Bind]
mg_drop :: Int -> MatchGroup GhcTc (LHsExpr GhcTc) -> MatchGroup GhcTc (LHsExpr GhcTc)
mg_flip :: MatchGroup GhcTc (LHsExpr GhcTc) -> MatchGroup GhcTc (LHsExpr GhcTc)
varString :: Id -> String
varTyConName :: Id -> Maybe String
