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

bind_to_table :: HsBind GhcTc -> Binds
bind_to_table b = case b of
  AbsBinds { abs_exports, abs_binds } ->
    let subbinds = mconcat $ bagToList $ mapBag (bind_to_table . unLoc) abs_binds -- consider making union_sym_table just Foldable t => ...
    in subbinds <> map (VarPat NoExt . noLoc . abe_poly &&& pure . noLoc . HsVar NoExt . noLoc . abe_mono) abs_exports
    
  -- AbsBindsSig { abs_sig_export, abs_sig_bind = L _ abs_sig_bind } -> 
  --   let subbinds = bind_to_table stack abs_sig_bind
  --   in subbinds {
  --       pms_syms = uncurry (insert abs_sig_export) $ (foldr (++) [] &&& id) $ pms_syms subbinds
  --     }
  
  -------------------
  -- SYM BASE CASE --
  -------------------
  FunBind { fun_id = fun_id, fun_matches } -> [( VarPat NoExt fun_id, [noLoc $ HsLam NoExt fun_matches] )]
  
  PatBind { pat_lhs = L _ pat_lhs, pat_rhs } ->
    grhs_binds' pat_rhs <> [(pat_lhs, grhs_exprs pat_rhs)]
  VarBind{} -> mempty
  _ -> error $ constr_ppr b

-- gmapQ :: Data c => (forall d. Data d => d -> e) -> c -> [e]
-- uncurried: Data c => ((forall d. Data d => d -> e), c) -> [e]
grhs_exprs :: GenericQ [LHsExpr GhcTc]
grhs_exprs x = map (\(L _ (GRHS _ _ body) :: LGRHS GhcTc (LHsExpr GhcTc)) -> body) (concat $ shallowest cast x)

type Binds = [(Pat GhcTc, [Sym])]
grhs_binds :: Stack -> GenericQ PatMatchSyms
grhs_binds st z =
  let binds = grhs_binds' z
      sub :: SymTable -> SymApp -> [SymApp]
      sub t sa =
        let m_next_args = map (map (sub t)) (sa_args sa)
            args_changed = any (any (not . null)) m_next_args
            next_args = map (concatMap (uncurry list_alt . second pure) . uncurry zip) (zip m_next_args (sa_args sa)) -- encode law that arguments can fail to reduce and just fall back to the original form
            m_next_syms :: Maybe (Maybe [SymApp])
            -- the only case where the iteration moves forward is when the matching finds a symbol that isn't just references to other symbols after reduction. `sub` could communicate this by just returning new symbols. Still ambiguous on the meaning if we succeed on some bare arguments. But by pattern matching, this could yield new things if the only path to that new binding was through that route, so arguments are preserved if they fail, as opposed to failing the whole block; only if all arguments fail and the symbol resolution fails, basically if _anything_ makes any progress, then we're good
            m_next_syms = case unLoc $ sa_sym sa of
              HsVar _ (L _ v) -> if not $ v `elem` (var_ref_tail $ sa_stack sa)
                then Just $
                  (
                      uncurry list_alt
                      . (concatMap (sub t) &&& id)
                      . map (\sa' ->
                          sa' {
                            sa_stack = append_frame (VarRefFrame v) (sa_stack sa'),
                            sa_args = (sa_args sa') <> next_args
                          }
                        )
                    )
                  <$> (t !? v)
                else Nothing
              _ -> Just Nothing
        in fromMaybe [] (fromMaybe (
            if args_changed
              then [sa { sa_args = next_args }]
              else [] -- encode the law that if all arguments have failed and the sym has also failed, this whole match fails
          ) <$> m_next_syms) -- encode the law that if this is a var reduction cycle, then the result is empty
      
      -- BOOKMARK need reduce_deep here, maybe strip away from pat_match for performance later
      
      iterant :: [(Pat GhcTc, [SymApp])] -> PatMatchSyms -> (Bool, ([(Pat GhcTc, [SymApp])], PatMatchSyms))
      iterant binds' pms =
        let next_pms = fromMaybe mempty $ mconcat $ map (mconcat . uncurry map . first pat_match) binds'
            syms = map snd binds'
            m_next_syms = map (map (sub (pms_syms next_pms))) syms
            changed = any (any (not . null)) m_next_syms
            next_syms = map (uncurry $ second . ((concatMap (uncurry list_alt . second pure)).) . zip) (zip m_next_syms binds')
        in (not changed, (next_syms, (pms <> next_pms) {
          pms_syms = pms_syms next_pms `map_alt` pms_syms pms
        })) -- look for if `<>` is the right thing to do on this pms chain
      binds0 = map (second (mconcat . map (reduce_deep . (flip (SA [] st) [])))) binds
      syms0 = mconcat $ map snd binds0
      symsn = snd $ snd $ until fst (uncurry iterant . snd) (False, (map (second rs_syms) binds0, mempty))
  in symsn { -- BOOKMARK this initial condition is really ugly
      pms_holds = pms_holds symsn <> rs_holds syms0,
      pms_writes = pms_writes symsn <> rs_writes syms0
    }

grhs_binds' :: GenericQ Binds -- TODO consider passing more info via `GenericQ (Maybe PatMatchSyms)`, and removing the fromMaybe
grhs_binds' = everythingBut (<>) (
    (mempty, False)
    `mkQ` ((,True) . bind_to_table)
    `extQ` ((,False) . ((\case
        BindStmt _ (L _ pat) expr _ _ -> [(pat, [expr])] -- TODO check if a fresh stack key here is the right thing to do
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