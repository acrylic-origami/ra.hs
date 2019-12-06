{-# LANGUAGE Rank2Types, ScopedTypeVariables, MultiWayIf, LambdaCase, NamedFieldPuns #-}

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
  get_mg_type,
  get_expr_type,
  inst_subty
) where

import GHC
import qualified GHC ( TyCon )
import TcEvidence ( HsWrapper(..) )
import ConLike ( ConLike(..) )
import DataCon ( DataCon(..), dataConRepType )
import qualified TyCon as GHCTyCon ( tyConName, tyConSingleDataCon_maybe )
import Type ( tyConAppTyConPicky_maybe, dropForAlls, splitFunTys, splitAppTys, splitTyConApp_maybe, isTyVarTy, getTyVar_maybe, tyConAppTyCon_maybe )
import DataCon ( dataConUserTyVarBinders )
import Var ( varName, varType )
import Name ( mkSystemName, nameOccName )
import OccName ( mkVarOcc, occNameString )
import Bag

-- for blank_id
import Type ( mkTyVarTy, mkFunTys )
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

get_mg_type :: MatchGroup GhcTc (LHsExpr GhcTc) -> Type
get_mg_type mg = uncurry mkFunTys $ (mg_arg_tys &&& mg_res_ty) $ mg_ext mg -- questioning why they didn't just give us a FunTy...

get_expr_type :: LHsExpr GhcTc -> Type
get_expr_type expr = case unLoc expr of
  -- TERMINAL SYMBOLS
  HsLamCase _ mg -> get_mg_type mg
  HsLam _ mg -> get_mg_type mg
  HsVar _ (L _ v) -> varType v
  HsOverLit _ (OverLit { ol_ext = OverLitTc { ol_type } }) -> ol_type
  HsOverLit _ (XOverLit _ ) -> blank_type
  HsLit _ _ -> blank_type
  ExplicitTuple _ args _ -> mkAppTys (error "Report this bug: too lazy to make actual Tuple TyCon.") (map (\case
        L _ (Present _ expr) -> get_expr_type expr
        _ -> error "Tuple sections not yet supported"
      ) args)
  ExplicitList ty _ _ -> ty
  HsConLikeOut _ (RealDataCon con) -> dataConRepType con -- TODO what's a PatSynCon again?
  
  -- NON-TERMINAL SYMBOLS
  -- NOTE: none of these should actually ever be called, because we should always have normal forms at instance resolution
  HsApp _ l _ -> uncurry mkFunTys $ first tail $ splitFunTysLossy $ get_expr_type l
  OpApp _ _ op _ -> uncurry mkFunTys $ first (tail . tail) $ splitFunTysLossy $ get_expr_type op
  HsWrap _ _ expr' -> get_expr_type $ expr' <$ expr
  NegApp _ expr' _ -> get_expr_type expr'
  HsPar _ expr' -> get_expr_type expr'
  SectionL _ _ op -> uncurry mkFunTys $ first tail $ splitFunTysLossy $ get_expr_type op
  SectionR _ op _ ->
    let op_ty = get_expr_type op
        (arg_tys, res_ty) = splitFunTysLossy op_ty
    in if length arg_tys > 0
      then mkFunTys (uncurry (:) $ (head &&& tail . tail) arg_tys) res_ty
      else undefined -- error $ (ppr_unsafe op_ty ++ "\n---\n" ++ constr_ppr op_ty)
  HsCase _ _ mg -> get_mg_type mg
  HsIf _ _ _ a _b -> get_expr_type a -- assume a ~ _b
  HsMultiIf ty _ -> ty
  HsLet _ _ ret -> get_expr_type ret
  HsDo ty _ _ -> ty
  ExprWithTySig _ expr' -> get_expr_type expr'
  HsAppType _ expr' -> get_expr_type expr'
  _ -> error $ show $ toConstr $ unLoc expr

strip_context :: Type -> Maybe Type
strip_context ty =
  let (args, ret) = splitFunTys ty
      n_ctx = takeWhile (isJust . join . fmap (listToMaybe . dataConUserTyVarBinders) . (GHCTyCon.tyConSingleDataCon_maybe=<<) . tyConAppTyCon_maybe) args
  in if length n_ctx > 0
    then Just $ mkFunTys (drop (length n_ctx) args) ret
    else Nothing

splitFunTysLossy :: Type -> ([Type], Type)
splitFunTysLossy z = splitFunTys (fromMaybe z (strip_context z))

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