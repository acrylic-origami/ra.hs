{-# LANGUAGE Rank2Types, ScopedTypeVariables, LambdaCase, TupleSections, NamedFieldPuns #-}
module Ra.GHC (
  grhs_exprs,
  grhs_binds,
  bind_to_table,
  mg_drop,
  mg_flip,
  varString
) where

import GHC
import Var ( varName )
import Bag

import Data.Generics ( everythingBut, GenericQ, cast, mkQ, extQ )
import Data.Generics.Extra ( shallowest, constr_ppr )
import Data.Tuple.Extra ( second, (&&&) )
import Data.Maybe ( catMaybes )
import Data.Semigroup ( mappend, (<>) )
import Data.Map.Strict ( unionWith, unionsWith, insert, singleton, empty, fromList, (!?) )

import Ra ( pat_match )
import Ra.Stack ( Sym, SymTable, PatMatchSyms(..), StackBranch, pms_syms, pms_writes, union_sym_tables )
import Ra.Extra

bind_to_table :: StackBranch -> HsBind Id -> PatMatchSyms
bind_to_table branch b = case b of
  AbsBinds { abs_exports, abs_binds } ->
    let subbinds = mconcat $ bagToList $ mapBag (bind_to_table branch . unLoc) abs_binds -- consider making union_sym_table just Foldable t => ...
    in subbinds <> mempty {
        pms_syms = fromList $ catMaybes $ map (\expr -> (abe_poly expr,) <$> (pms_syms subbinds !? abe_mono expr)) abs_exports
      }
  AbsBindsSig { abs_sig_export, abs_sig_bind = L _ abs_sig_bind } -> 
    let subbinds = bind_to_table branch abs_sig_bind
    in subbinds {
        pms_syms = uncurry (insert abs_sig_export) $ (foldr (++) [] &&& id) $ pms_syms subbinds
      }
  FunBind { fun_id = L _ fun_id, fun_matches } -> mempty {
      pms_syms = singleton fun_id [HsLam fun_matches]
    }
  PatBind { pat_lhs = L _ pat_lhs, pat_rhs } ->
    let PatMatchSyms next_explicit_binds bind_writes = grhs_binds branch pat_rhs
        branch' = update_head (second (union_sym_tables . (:[next_explicit_binds]))) branch
        next_exprs = grhs_exprs pat_rhs
        next_tables = map (pat_match branch' pat_lhs) next_exprs
    in mempty { pms_writes = bind_writes } <> mconcat next_tables
  VarBind{} -> mempty
  _ -> error $ constr_ppr b
    
grhs_exprs :: GenericQ [HsExpr Id]
grhs_exprs x = map (\(L _ (GRHS _ body) :: LGRHS Id (LHsExpr Id)) -> unLoc body) (concat $ shallowest cast x)
grhs_binds :: StackBranch -> GenericQ PatMatchSyms
grhs_binds branch =
  let go is_do = uncurry (bool mempty) . (
      uncurry (<>) . (
        -- cat the results from the current iteration with the [maybe] recursion
          uncurry gmapQ . (
            -- split the element down to the recursion `go` with a decision if it's a `do` or not, and the element itself
              go . (is_do `mkQ` ((\case
                  HsDo _ _ _ -> True
                  _ -> False
                ) :: HsExpr Id -> Bool))
              &&& id
            )
            &&& mempty
              `mkQ` bind_to_table branch
              `extQ` ((\case
                  BindStmt (L _ pat) (L _ expr) _ _ _ -> pat_match branch pat expr
                  _ -> mempty
                ) . unLoc :: LStmt Id (LHsExpr Id) -> PatMatchSyms)
              `extQ` ((\case 
                  HsApp _ _ -> True
                  HsLam _ -> True
                  -- HsDo _ _ _ -> True -- DONE: thought further. Will extend with case only for `let` stmts -- TODO dubious case: think further
                  _ -> False 
                ) :: HsExpr Id -> Bool)
        )
      &&& True `mkQ` ((\case 
        -- provide the boolean guard for the places we stop
        -- opposite polarity of `everythingBut` because of the partial on `bool`
        HsApp _ _ -> False
        HsLam _ -> False
        -- HsDo _ _ _ -> True -- DONE: thought further. Will extend with case only for `let` stmts -- TODO dubious case: think further
        _ -> False 
      ) :: HsExpr Id -> Bool)
    )
  in go False

mg_rearg :: (forall a. [a] -> [a]) -> MatchGroup Id (LHsExpr Id) -> MatchGroup Id (LHsExpr Id)
mg_rearg f mg = mg {
  mg_alts = (map ((\match -> match { m_pats = f (m_pats match) })<$>)
    ) <$> mg_alts mg
  , mg_arg_tys = f (mg_arg_tys mg)
}

mg_drop x = mg_rearg $ drop x -- i don't see why i couldn't do `mg_rearg . drop` but the typechecker complained because the type became rigid

mg_flip = mg_rearg (\(a:b:ns) -> b:a:ns)

varString = occNameString . nameOccName . varName