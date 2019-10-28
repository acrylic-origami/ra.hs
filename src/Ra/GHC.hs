{-# LANGUAGE Rank2Types, ScopedTypeVariables, LambdaCase, TupleSections, NamedFieldPuns #-}
module Ra.GHC (
  Binds,
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
import Data.Tuple.Extra ( first, second, (&&&), (***) )
import Data.Maybe ( catMaybes, fromMaybe )
import Data.Monoid ( mempty, mconcat )
import Data.Semigroup ( (<>) )
import Data.Map.Strict ( unionWith, unionsWith, insert, singleton, empty, fromList, (!?) )

import Control.Applicative ( liftA2 )

import Ra ( pat_match, reduce_deep )
import Ra.Lang -- ( Stack(..), SymApp(..), Sym(..), SymTable(..), PatMatchSyms(..), ReduceSyms(..), StackBranch(..), unSB, mapSB, union_sym_tables, make_stack_key )
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

bind_to_table :: Stack -> HsBind GhcTc -> Binds
bind_to_table st b = case b of
  AbsBinds { abs_exports, abs_binds } ->
    let subbinds = mconcat $ bagToList $ mapBag (bind_to_table st . unLoc) abs_binds
    in subbinds <> map (
        VarPat NoExt . noLoc . abe_poly
        &&& reduce_deep . ((flip (SA [] st)) []) . noLoc . HsVar NoExt . noLoc . abe_mono
      ) abs_exports
    
  -- AbsBindsSig { abs_sig_export, abs_sig_bind = L _ abs_sig_bind } -> 
  --   let subbinds = bind_to_table stack abs_sig_bind
  --   in subbinds {
  --       pms_syms = uncurry (insert abs_sig_export) $ (foldr (++) [] &&& id) $ pms_syms subbinds
  --     }
  
  -------------------
  -- SYM BASE CASE --
  -------------------
  FunBind { fun_id = fun_id, fun_matches } -> [(
      VarPat NoExt fun_id,
      mempty {
        rs_syms = [SA [] st (noLoc $ HsLam NoExt fun_matches) []]
      }
    )]
  
  PatBind { pat_lhs = L _ pat_lhs, pat_rhs } ->
    grhs_binds st pat_rhs <> [(
        pat_lhs,
        mconcat $ map (reduce_deep . flip (SA [] st) []) (grhs_exprs pat_rhs)
      )]
  VarBind{} -> mempty
  _ -> error $ constr_ppr b

-- gmapQ :: Data c => (forall d. Data d => d -> e) -> c -> [e]
-- uncurried: Data c => ((forall d. Data d => d -> e), c) -> [e]
grhs_exprs :: GenericQ [LHsExpr GhcTc]
grhs_exprs x = map (\(L _ (GRHS _ _ body) :: LGRHS GhcTc (LHsExpr GhcTc)) -> body) (concat $ shallowest cast x)

grhs_binds :: Stack -> GenericQ Binds -- TODO consider passing more info via `GenericQ (Maybe PatMatchSyms)`, and removing the fromMaybe
grhs_binds st = everythingBut (<>) (
    (mempty, False)
    `mkQ` ((,True) . bind_to_table st)
    `extQ` ((,False) . ((\case
        BindStmt _ (L _ pat) expr _ _ -> [(pat, reduce_deep (SA [] st expr []))]
        _ -> mempty
      ) . unLoc :: LStmt GhcTc (LHsExpr GhcTc) -> Binds)) -- TODO dangerous: should we really keep looking deeper after finding a BindStmt?
    `extQ` ((mempty,) . ((\case 
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

mg_drop x = mg_rearg $ drop x

mg_flip = mg_rearg (\(a:b:ns) -> b:a:ns)

varString = occNameString . nameOccName . varName
varTyConName = fmap (occNameString . nameOccName . GHCTyCon.tyConName) . tyConAppTyConPicky_maybe . snd . splitForAllTys . varType

-- instance Applicative (GenLocated a) where
--   pure = L noLoc
--   (<*>) (L l f) = L l . fmap f