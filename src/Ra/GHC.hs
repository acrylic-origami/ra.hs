{-# LANGUAGE Rank2Types, ScopedTypeVariables, LambdaCase, TupleSections, NamedFieldPuns #-}
module Ra.GHC (
  deapp,
  unHsWrap,
  grhs_exprs,
  grhs_binds,
  bind_to_table,
  mg_drop,
  mg_flip,
  varString,
  varTyConName
) where

import GHC
import qualified GHC ( TyCon )
import qualified TyCon as GHCTyCon ( tyConName )
import Type ( tyConAppTyConPicky_maybe )
import Var ( varName, varType )
import Name ( mkSystemName, nameOccName )
import OccName ( mkVarOcc, occNameString )
import Bag

import Data.Generics ( Data(..), everythingBut, GenericQ, cast, mkQ, extQ, gmapQ )
import Data.Generics.Extra ( shallowest, constr_ppr )
import Data.Bool ( bool )
import Data.Tuple.Extra ( second, (&&&), (***) )
import Data.Maybe ( catMaybes, fromMaybe )
import Data.Monoid ( mempty, mconcat )
import Data.Semigroup ( (<>) )
import Data.Map.Strict ( unionWith, unionsWith, insert, singleton, empty, fromList, (!?) )

import Control.Applicative ( liftA2 )

import Ra ( pat_match )
import Ra.Lang ( Stack(..), SymApp(..), Sym(..), SymTable(..), PatMatchSyms(..), StackBranch(..), unSB, mapSB, union_sym_tables, make_stack_key )
import Ra.Extra

unHsWrap :: LHsExpr GhcTc -> LHsExpr GhcTc
unHsWrap expr = case unLoc expr of
  HsWrap _ _ v -> unHsWrap (fmap (const v) expr)
  _ -> expr

deapp :: LHsExpr GhcTc -> (LHsExpr GhcTc, [LHsExpr GhcTc])
deapp expr =
  let unwrapped = unHsWrap expr
  in case unLoc unwrapped of
    HsApp _ l r -> (id *** (++[r])) (deapp l)
    _ -> (unwrapped, [])

bind_to_table :: Stack -> HsBind GhcTc -> PatMatchSyms -- TODO PatMatchSyms without `Maybe` is an aggressive assertion, losing information. Reconsider.
bind_to_table stack b = case b of
  AbsBinds { abs_exports, abs_binds } ->
    let subbinds = mconcat $ bagToList $ mapBag (bind_to_table stack . unLoc) abs_binds -- consider making union_sym_table just Foldable t => ...
    in subbinds <> mempty {
        pms_syms = fromList $ catMaybes $ map (\expr -> (abe_poly expr,) <$> (pms_syms subbinds !? abe_mono expr)) abs_exports
      }
  -- AbsBindsSig { abs_sig_export, abs_sig_bind = L _ abs_sig_bind } -> 
  --   let subbinds = bind_to_table stack abs_sig_bind
  --   in subbinds {
  --       pms_syms = uncurry (insert abs_sig_export) $ (foldr (++) [] &&& id) $ pms_syms subbinds
  --     }
  
  -------------------
  -- SYM BASE CASE --
  -------------------
  FunBind { fun_id = L _ fun_id, fun_matches } -> mempty {
      pms_syms = singleton fun_id [ SA {
          sa_stack = stack,
          sa_consumers = mempty,
          sa_sym = noLoc $ HsLam NoExt fun_matches,
          sa_args = []
        } ]
    }
  PatBind { pat_lhs = L _ pat_lhs, pat_rhs } ->
    let pms@(PatMatchSyms {
          pms_syms = next_explicit_binds,
          pms_writes = bind_writes
        }) = grhs_binds stack pat_rhs
        stack' = stack {
            st_branch = mapSB (update_head (second (union_sym_tables . (:[next_explicit_binds])))) (st_branch stack)
          }
        next_exprs = grhs_exprs pat_rhs
        next_pms = mconcat $ catMaybes $ map (pat_match pat_lhs . flip (SA [] stack') []) next_exprs -- TODO confirm that making a fresh stack key here is the right thing to do
    in pms { pms_syms = mempty } <> next_pms
  VarBind{} -> mempty
  _ -> error $ constr_ppr b

-- gmapQ :: Data c => (forall d. Data d => d -> e) -> c -> [e]
-- uncurried: Data c => ((forall d. Data d => d -> e), c) -> [e]
grhs_exprs :: GenericQ [LHsExpr GhcTc]
grhs_exprs x = map (\(L _ (GRHS _ _ body) :: LGRHS GhcTc (LHsExpr GhcTc)) -> body) (concat $ shallowest cast x)
grhs_binds :: Stack -> GenericQ PatMatchSyms -- TODO consider passing more info via `GenericQ (Maybe PatMatchSyms)`, and removing the fromMaybe
grhs_binds stack = fromMaybe mempty . everythingBut (<>) (
    (Nothing, False)
    `mkQ` ((,True) . Just . bind_to_table stack)
    `extQ` ((,False) . ((\case
        BindStmt _ (L _ pat) expr _ _ -> pat_match pat (SA [] stack expr []) -- TODO check if a fresh stack key here is the right thing to do
        _ -> Nothing
        ) . unLoc :: LStmt GhcTc (LHsExpr GhcTc) -> Maybe PatMatchSyms)) -- TODO dangerous: should we really keep looking deeper after finding a BindStmt?
    `extQ` ((Nothing,) . ((\case 
      HsApp _ _ _ -> True
      HsLam _ _ -> True
      _ -> False 
    ) :: HsExpr GhcTc -> Bool)) -- guard against applications and lambdas, which introduce bindings we need to dig into a scope to bind
  )

mg_rearg :: (forall a. [a] -> [a]) -> MatchGroup GhcTc (LHsExpr GhcTc) -> MatchGroup GhcTc (LHsExpr GhcTc)
mg_rearg f mg = mg {
  mg_alts = (map ((\match -> match { m_pats = f (m_pats match) })<$>)
    ) <$> mg_alts mg
  , mg_ext = (mg_ext mg) {
      mg_arg_tys = f $ mg_arg_tys $ mg_ext mg
    }
}

mg_drop x = mg_rearg $ drop x -- i don't see why i couldn't do `mg_rearg . drop` but the typechecker complained because the type became rigid

mg_flip = mg_rearg (\(a:b:ns) -> b:a:ns)

varString = occNameString . nameOccName . varName
varTyConName = fmap (occNameString . nameOccName . GHCTyCon.tyConName) . tyConAppTyConPicky_maybe . snd . splitForAllTys . varType

-- instance Applicative (GenLocated a) where
--   pure = L noLoc
--   (<*>) (L l f) = L l . fmap f