module Ra.GHC (
  grhs_exprs,
  grhs_binds,
  bind_to_table,
  mg_drop
) where

import GHC
import Data.Generics

import Ra.Stack ( SymTable, StackBranch )
import Ra.Extra

bind_to_table :: StackBranch -> HsBind Id -> SymTable
grhs_exprs :: GenericQ [HsExpr Id]
grhs_binds :: GenericQ SymTable
mg_drop :: Int -> MatchGroup Id (LHsExpr Id) -> MatchGroup Id (LHsExpr Id)