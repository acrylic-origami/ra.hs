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
  -- blank_type,
  -- blank_id,
  get_mg_type,
  get_expr_type,
  strip_context,
  strip_contexts_deep,
  splitFunTysLossy,
  inst_subty
) where

import GHC
import qualified GHC ( TyCon )
import TcEvidence ( HsWrapper(..) )
import ConLike ( ConLike(..) )
import DataCon ( DataCon(..), dataConRepType )
import qualified TyCon as GHCTyCon ( tyConName, tyConSingleDataCon_maybe )
import Type ( tyConAppTyConPicky_maybe, dropForAlls, splitFunTys, splitFunTy_maybe, mkInvForAllTy, splitAppTys, splitAppTy_maybe, mkAppTys, mkFunTy, splitTyConApp_maybe, isTyVarTy, mkTyVarTy, getTyVar_maybe, tyConAppTyCon_maybe, splitForAllTy_maybe, eqType )
import DataCon ( dataConUserTyVarBinders )
import Var ( varName, varType, setVarType )
import Name ( mkSystemName, nameOccName )
import OccName ( mkVarOcc, occNameString )
import Bag

-- for blank_id
import Data.List ( elemIndex )
import Type ( mkTyVarTy, mkFunTys )
import Name ( mkSystemName )
import OccName ( mkVarOcc )
import Unique ( mkVarOccUnique )
import FastString ( mkFastString ) 
import Var ( mkLocalVar )
import IdInfo ( vanillaIdInfo, IdDetails(VanillaId) )

import Data.Foldable ( foldrM )
import Data.Generics ( Data(..), everywhere, mkT, extT, GenericT, everythingBut, GenericQ, cast, mkQ, extQ, gmapQ )
import Data.Generics.Extra ( shallowest, constr_ppr )
import Data.Bool ( bool )
import qualified Data.Map.Strict as M
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
  HsWrap _ w expr' ->
    let tymapper :: HsWrapper -> Type -> (Type, [(Id, Type)])
        tymapper w' ty
          | Just ty' <- strip_context ty
          = tymapper w' ty'
          | otherwise
          = case w' of
            WpTyApp ty'
              | Just (tyvar, ty_rest) <- splitForAllTy_maybe ty
              -> (ty_rest, [(tyvar, ty')])
            WpCompose l r ->
              let ((ty', rl), rr) = first (tymapper l) (tymapper r ty) -- right-left application of concrete ev vars
              in (ty', rl <> rr)
            _ -> (ty, [])
        expr'' = snd ((w), unHsWrap (expr' <$ expr))
        tymap = M.fromList $ snd $ tymapper w $ get_expr_type expr''
        tf :: GenericT
        tf = mkT (\t ->
            case getTyVar_maybe t of
              Just v | Just t' <- v `M.lookup` tymap -> t'
              _ -> t
          )
    in everywhere (tf `extT` (\v -> setVarType v $ everywhere tf $ varType v)) expr'' -- leave the foralls intact: they'll be disassembled by inst_subty and other funs that touch types directly
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
-- blank_type = mkTyVarTy blank_id
-- blank_id = mkLocalVar VanillaId blank_name blank_type vanillaIdInfo

get_mg_type :: MatchGroup GhcTc (LHsExpr GhcTc) -> Type
get_mg_type mg = uncurry mkFunTys $ (mg_arg_tys &&& mg_res_ty) $ mg_ext mg -- questioning why they didn't just give us a FunTy...

get_expr_type :: LHsExpr GhcTc -> Type
get_expr_type expr = case unLoc expr of
  -- TERMINAL SYMBOLS
  HsLamCase _ mg -> get_mg_type mg
  HsLam _ mg -> get_mg_type mg
  HsVar _ (L _ v) -> varType v
  HsOverLit _ (OverLit { ol_ext = OverLitTc { ol_type } }) -> ol_type
  HsOverLit _ (XOverLit _ ) -> error "Type unextractable from XOverLit"
  HsLit _ _ -> error "Type unextractable from HsLit "
  ExplicitTuple _ args _ -> mkAppTys (error "Report this bug: too lazy to make actual Tuple TyCon.") (map (\case
        L _ (Present _ expr') -> get_expr_type expr'
        _ -> error "Tuple sections not yet supported"
      ) args)
  ExplicitList ty _ _ -> ty
  HsConLikeOut _ (RealDataCon con) -> dataConRepType con -- TODO what's a PatSynCon again?
  
  -- NON-TERMINAL SYMBOLS
  -- NOTE: none of these should actually ever be called, because we should always have normal forms at instance resolution
  HsApp _ l _ -> drop_ty_args [0] $ strip_contexts_deep $ get_expr_type l
  OpApp _ _ op _ -> drop_ty_args [0, 1] $ strip_contexts_deep $ get_expr_type op
  HsWrap _ _ expr' -> get_expr_type $ expr' <$ expr
  NegApp _ expr' _ -> get_expr_type expr'
  HsPar _ expr' -> get_expr_type expr'
  SectionL _ _ op -> drop_ty_args [0] $ strip_contexts_deep $ get_expr_type op
  SectionR _ op _ -> drop_ty_args [1] $ strip_contexts_deep $ get_expr_type op
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
      n_ctx = takeWhile (fromMaybe False . fmap isClassTyCon . tyConAppTyCon_maybe) args
  in if length n_ctx > 0
    then Just $ mkFunTys (drop (length n_ctx) args) ret
    else Nothing

strip_contexts_deep :: GenericT
strip_contexts_deep = everywhere (mkT $ \z -> fromMaybe z (strip_context z))

splitFunTysLossy :: Type -> ([Type], Type)
splitFunTysLossy = splitFunTys . strip_contexts_deep

drop_ty_args :: [Int] -> Type -> Type
drop_ty_args = drop_ty_args' 0 where
  drop_ty_args' n idxs ty
    | null idxs = ty
    | Just (bndr, ty') <- splitForAllTy_maybe ty
    = mkInvForAllTy bndr (drop_ty_args' n idxs ty')
    | Just (arg_ty, ty') <- splitFunTy_maybe ty
    = case elemIndex n idxs of
      Just idx -> drop_ty_args' (n + 1) (take idx idxs ++ drop (idx + 1) idxs) ty'
      Nothing -> mkFunTy arg_ty (drop_ty_args' (n + 1) idxs ty')
    | otherwise = error "Not enough args to pop"

inst_subty :: Type -> Type -> Maybe (Map Id Type)
inst_subty a b =
  let ((fun_tys_a, a'), (fun_tys_b, b')) = both (splitFunTysLossy . everywhere (mkT dropForAlls)) (a, b)
      ((m_app_con_a, m_app_tys_a), (m_app_con_b, m_app_tys_b)) = both (\ty ->
          let (m_con, m_tys) = (fmap fst &&& fmap snd) $ splitAppTy_maybe ty
              m_con_tys' = splitAppTys <$> m_con
          in (fst <$> m_con_tys', liftA2 ((.pure) . (<>) . snd) m_con_tys' m_tys)
        ) (a', b') -- NOTE also splits funtys annoyingly
      
      masum = foldrM (flip (fmap . union) . uncurry inst_subty) mempty
  in snd ((a, b, a', b', m_app_con_a, m_app_tys_a, m_app_con_b, m_app_tys_b, fun_tys_a, fun_tys_b),
      if | not $ null fun_tys_a -> -- function type matching
          if length fun_tys_b < length fun_tys_a
            then Nothing -- candidate function doesn't necessarily return function (unless it's `forall`; TODO)
            else
              union <$> inst_subty a' (mkFunTys (drop (length fun_tys_a) fun_tys_b) b') -- allow the possibility that the last term of `a` captures a return function from `b`: i.e. `a :: c` matches `b :: d -> e`
              <*> masum (zip fun_tys_a fun_tys_b)
         | Just (tycon_a, tyargs_a) <- splitTyConApp_maybe a -- `a` is a true TyCon
         -> case splitTyConApp_maybe b of
          Just (tycon_b, tyargs_b)
            | tycon_a == tycon_b -> masum $ zip tyargs_a tyargs_b
            | otherwise -> Nothing
          Nothing -> case m_app_con_a >>= splitTyConApp_maybe of
            Just (tycon_b, tyargs_b)
              | tycon_a == tycon_b -> masum $ zip tyargs_a tyargs_b
              | otherwise -> Nothing
            Nothing -> Nothing
         | Just avar <- getTyVar_maybe a' ->
          if not $ isTyVarTy b'
            then Just (singleton avar b') -- beta-reduction
            else Just mempty
         | isJust (m_app_con_a >>= splitTyConApp_maybe) -- `a'` may be an application of TyCon on concrete vars: 
         , not $ fromMaybe False (liftA2 eqType m_app_con_a m_app_con_b)
         -> Nothing -- `a` is more concrete than `b` or their tycons are incompatible
         | otherwise -> -- `a` is probably a generic AppTy (e.g. `m a`)
            do
              args <- snd ((a, b, a', b', m_app_con_a, m_app_tys_a, m_app_con_b, m_app_tys_b, fun_tys_a, fun_tys_b), liftA2 zip m_app_tys_a m_app_tys_b) -- dubiously lenient on matching these tyvars... can we assert the same way that `a`'s need to be more general than `b`'s always?
              conmap <- join $ liftA2 inst_subty m_app_con_a m_app_con_b
              argmap <- masum args
              return $ union conmap argmap
    )
      
      -- &&  -- DEBUG
      -- then args_eq fa_tys_a -- instance type equality assumes that the only things that matter are that one type is more concrete than the other, as well as basic function "subtyping" (i.e. we won't ever be asked if `m (forall a. a -> a) <: m (a -> a)` because we can't create a constraint at a class/data site like `class Foo (a -> b)`)
  -- enforce parity implicitly, via flipping bool at every checkpoint