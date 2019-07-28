{-# LANGUAGE Rank2Types #-}
module Ra.GHC (
  grhs_exprs,
  grhs_binds,
  bind_to_table,
  mg_drop,
  mg_flip
) where

import GHC
import Data.Generics

import Ra.Stack ( SymTable, StackBranch )
import Ra.Extra

bind_to_table :: StackBranch -> HsBind Id -> SymTable
grhs_exprs :: GenericQ [HsExpr Id]
grhs_binds :: StackBranch -> GenericQ SymTable
mg_drop :: Int -> MatchGroup Id (LHsExpr Id) -> MatchGroup Id (LHsExpr Id)
mg_flip :: MatchGroup Id (LHsExpr Id) -> MatchGroup Id (LHsExpr Id)