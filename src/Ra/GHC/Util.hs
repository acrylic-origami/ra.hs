{-# LANGUAGE Rank2Types, ScopedTypeVariables, MultiWayIf #-}

module Ra.GHC.Util (
  unHsWrap,
  deapp,
  grhs_exprs,
  mg_rearg,
  mg_drop,
  mg_flip,
  varString,
  varTyConName,
  blank_name,
  blank_type,
  blank_id,
  inst_subty
) where

import GHC
import qualified GHC ( TyCon )
import qualified TyCon as GHCTyCon ( tyConName, tyConSingleDataCon_maybe )
import Type ( tyConAppTyConPicky_maybe, dropForAlls, splitFunTys, splitAppTys, splitTyConApp_maybe, isTyVarTy, getTyVar_maybe, tyConAppTyCon_maybe )
import DataCon ( dataConUserTyVarBinders )
import Var ( varName, varType )
import Name ( mkSystemName, nameOccName )
import OccName ( mkVarOcc, occNameString )
import Bag

-- for blank_id
import Type ( mkTyVarTy )
import Name ( mkSystemName )
import OccName ( mkVarOcc )
import Unique ( mkVarOccUnique )
import FastString ( mkFastString ) 
import Var ( mkLocalVar )
import IdInfo ( vanillaIdInfo, IdDetails(VanillaId) )

import Data.Foldable ( foldrM )
import Data.Generics ( Data(..), everythingBut, GenericQ, cast, mkQ, extQ, gmapQ )
import Data.Generics.Extra ( shallowest, constr_ppr )
import Data.Bool ( bool )
import Control.Arrow ( first, second, (&&&), (***) )
import Data.Maybe ( catMaybes, fromMaybe, isJust, listToMaybe )
import Control.Monad ( join )
import Data.Monoid ( mempty, mconcat )
import Data.Semigroup ( (<>) )
import Data.Map.Strict ( Map(..), union, unionWith, unionsWith, insert, singleton, empty, fromList, (!?) )
import Control.Applicative ( liftA2, Alternative(..) )

import Ra.Extra ( both )
-- import Control.Applicative.Alternative ( asum )

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
    
grhs_exprs :: GenericQ [LHsExpr GhcTc]
grhs_exprs x = map (\(L _ (GRHS _ _ body) :: LGRHS GhcTc (LHsExpr GhcTc)) -> body) (concat $ shallowest cast x)

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

blank_name = mkSystemName (mkVarOccUnique $ mkFastString "") (mkVarOcc "")
blank_type = mkTyVarTy blank_id
blank_id = mkLocalVar VanillaId blank_name blank_type vanillaIdInfo


inst_subty :: Type -> Type -> Maybe (Map Id Type)
inst_subty a b =
  let (a', b') = both dropForAlls (a, b)
      ((fun_tys_a, ret_a), (fun_tys_b, ret_b)) = both strip (a', b') where
        strip z =
          let full@(ctx_fun_tys, rhs) = splitFunTys $ dropForAlls z
              fun_tys = dropWhile (isJust . join . fmap (listToMaybe . dataConUserTyVarBinders) . (GHCTyCon.tyConSingleDataCon_maybe=<<) . tyConAppTyCon_maybe) ctx_fun_tys
          in if null ctx_fun_tys
            then full -- drop forall
            else first (fun_tys++) $ strip rhs
      ((app_con_a, app_tys_a), (app_con_b, app_tys_b)) = both splitAppTys (a', b') -- NOTE also splits funtys annoyingly
      ((m_tycon_a, m_tycon_tys_a), (m_tycon_b, m_tycon_tys_b)) = both ((fmap fst &&& fmap snd) . splitTyConApp_maybe) (a', b')
      
      masum = foldrM (flip (fmap . union) . uncurry inst_subty) mempty
  in if (isJust m_tycon_a)
      && fromMaybe True (liftA2 (/=) m_tycon_a m_tycon_b)
    then Nothing -- `a` is more concrete than `b` or their tycons are incompatible
    else fst (mempty, (a, b, a', b', app_con_a, app_con_b, fun_tys_a, fun_tys_b, ret_a, ret_b, (m_tycon_a, m_tycon_tys_a), (m_tycon_b, m_tycon_tys_b))) <> ( -- DEBUG
        if | Just avar <- getTyVar_maybe a' ->
            if not $ isTyVarTy b'
              then Just (singleton avar b') -- beta-reduction
              else Just mempty
           | not $ null fun_tys_a -> -- function type matching
            if length fun_tys_a /= length fun_tys_b
              then Nothing
              else
                union <$> inst_subty ret_a ret_b
                <*> masum (zip fun_tys_a fun_tys_b)
           | otherwise ->
            liftA2 union
              (fromMaybe (Just mempty) (
                  masum <$> liftA2 zip m_tycon_tys_a m_tycon_tys_b
                ))
              (masum (zip app_tys_a app_tys_b))
      )
      
      -- &&  -- DEBUG
      -- then args_eq fa_tys_a -- instance type equality assumes that the only things that matter are that one type is more concrete than the other, as well as basic function "subtyping" (i.e. we won't ever be asked if `m (forall a. a -> a) <: m (a -> a)` because we can't create a constraint at a class/data site like `class Foo (a -> b)`)
  -- enforce parity implicitly, via flipping bool at every checkpoint