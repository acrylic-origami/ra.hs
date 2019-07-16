{-# LANGUAGE LambdaCase, TupleSections, NamedFieldPuns #-}
module Ra.GHC (
  grhs_exprs,
  grhs_binds,
  bind_to_table,
  mg_drop,
  mg_flip
) where

import GHC
import Bag
import Data.Generics ( everythingBut, GenericQ, cast, mkQ, extQ )
import Data.Generics.Extra ( shallowest )
import Data.Tuple.Extra ( second )
import Data.Coerce (coerce)
import Data.Map.Strict ( unionWith, unionsWith, insert, singleton, empty )

import Ra ( pat_match )
import Ra.Stack ( Sym(..), SymTable(..), StackBranch, union_sym_tables, mksym )
import Ra.Extra

bind_to_table :: StackBranch -> HsBind Id -> SymTable
bind_to_table branch = \case
  AbsBinds { abs_binds } -> SymTable $ foldl (unionWith (++)) empty (mapBag (coerce . bind_to_table branch . unLoc) abs_binds)
  FunBind { fun_id = L _ fun_id, fun_matches } -> SymTable $ singleton fun_id [mksym (HsLam fun_matches)]
  PatBind { pat_lhs = L _ pat_lhs, pat_rhs } ->
    let branch' = update_head (second (union_sym_tables . (:[grhs_binds pat_rhs]))) branch
        next_exprs = grhs_exprs pat_rhs
        next_tables = map (\expr -> pat_match branch' expr pat_lhs) (map mksym next_exprs)
    in union_sym_tables next_tables
    
grhs_exprs :: GenericQ [HsExpr Id]
grhs_exprs = map (\(GRHS _ body) -> body) . concat . shallowest (cast :: GenericQ (Maybe (GRHS Id (HsExpr Id))))
grhs_binds :: GenericQ SymTable
grhs_binds = union_sym_tables . everythingBut (++) (
    ([SymTable empty], False)
    `mkQ` ((,False) . pure . bind_to_table undefined) -- TODO add branch here somehow
    `extQ` (([SymTable empty],) . ((\case 
      HsApp _ _ -> True
      HsLam _ -> True
      _ -> False 
    ) :: HsExpr Id -> Bool)) -- guard against applications and lambdas, which introduce bindings we need to dig into a scope to bind
  )

mg_drop :: Int -> MatchGroup Id (LHsExpr Id) -> MatchGroup Id (LHsExpr Id)
mg_drop num mg = mg {
  mg_alts = noLoc (map (\(L _ match) ->
      noLoc match { m_pats = drop num (m_pats match) }
    ) (unLoc $ mg_alts mg))
  , mg_arg_tys = drop num (mg_arg_tys mg)
}

mg_flip :: MatchGroup Id (LHsExpr Id) -> MatchGroup Id (LHsExpr Id)
mg_flip mg = mg {
  mg_alts = noLoc (map (\(L _ match) ->
      noLoc match { m_pats =
        let pats = m_pats match
        in (pats !! 2) : (pats !! 1) : drop 2 pats }
    ) (unLoc $ mg_alts mg))
  , mg_arg_tys =
    let tys = mg_arg_tys mg
    in (tys !! 2) : (tys !! 1) : drop 2 tys
}