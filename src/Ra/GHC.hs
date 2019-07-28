{-# LANGUAGE Rank2Types, ScopedTypeVariables, LambdaCase, TupleSections, NamedFieldPuns #-}
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
import Data.Generics.Extra ( shallowest, constr_ppr )
import Data.Tuple.Extra ( second, (&&&) )
import Data.Coerce (coerce)
import Data.Map.Strict ( unionWith, unionsWith, insert, singleton, empty )

import Ra ( pat_match )
import Ra.Stack ( Sym(..), SymTable(..), StackBranch, union_sym_tables, mksym )
import Ra.Extra

bind_to_table :: StackBranch -> HsBind Id -> SymTable
bind_to_table branch b = case b of
  AbsBinds { abs_binds } -> union_sym_tables $ bagToList $ mapBag (bind_to_table branch . unLoc) abs_binds -- consider making union_sym_table just Foldable t => ...
  AbsBindsSig { abs_sig_export, abs_sig_bind = L _ abs_sig_bind } -> SymTable $ uncurry (insert abs_sig_export) $ (foldr (++) [] &&& id) $ coerce $ bind_to_table branch abs_sig_bind
  FunBind { fun_id = L _ fun_id, fun_matches } -> SymTable $ singleton fun_id [mksym (HsLam fun_matches)]
  PatBind { pat_lhs = L _ pat_lhs, pat_rhs } ->
    let branch' = update_head (second (union_sym_tables . (:[grhs_binds branch pat_rhs]))) branch
        next_exprs = grhs_exprs pat_rhs
        next_tables = map (\expr -> pat_match branch' expr pat_lhs) (map mksym next_exprs)
    in union_sym_tables next_tables
  VarBind{} -> SymTable empty
  _ -> error $ constr_ppr b
    
grhs_exprs :: GenericQ [HsExpr Id]
grhs_exprs x = map (\(L _ (GRHS _ body) :: LGRHS Id (LHsExpr Id)) -> unLoc body) (concat $ shallowest cast x)
grhs_binds :: StackBranch -> GenericQ SymTable
grhs_binds branch = union_sym_tables . everythingBut (++) (
    ([SymTable empty], False)
    `mkQ` ((,False) . pure . bind_to_table branch)
    `extQ` (([SymTable empty],) . ((\case 
      HsApp _ _ -> True
      HsLam _ -> True
      _ -> False 
    ) :: HsExpr Id -> Bool)) -- guard against applications and lambdas, which introduce bindings we need to dig into a scope to bind
  )

mg_rearg :: (forall a. [a] -> [a]) -> MatchGroup Id (LHsExpr Id) -> MatchGroup Id (LHsExpr Id)
mg_rearg f mg = mg {
  mg_alts = (map ((\match -> match { m_pats = f (m_pats match) })<$>)
    ) <$> mg_alts mg
  , mg_arg_tys = f (mg_arg_tys mg)
}

mg_drop x = mg_rearg $ drop x -- i don't see why i couldn't do `mg_rearg . drop` but the typechecker complained because the type became rigid

mg_flip = mg_rearg (\(a:b:ns) -> b:a:ns)