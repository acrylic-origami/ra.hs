{-# LANGUAGE Rank2Types, LambdaCase, TupleSections, NamedFieldPuns #-}
module Ra.GHC.Translate (
  grhs_binds,
  bind_to_table,
) where

import GHC
import Bag ( bagToList, mapBag )

import Data.Generics ( GenericQ, mkQ, extQ, gmapQ, everythingBut)
import Data.Generics.Extra ( shallowest, constr_ppr )
import Control.Arrow ( (&&&) )

import Ra.Lang -- ( Stack(..), SymApp(..), Sym(..), SymTable(..), PatMatchSyms(..), ReduceSyms(..), Stack(..), unSB, mapSB, union_sym_tables, make_loc_key )
import Ra.GHC.Util ( grhs_exprs )
import Ra.Extra

bind_to_table :: Bool -> LHsBind GhcTc -> [Bind]
bind_to_table with_abs_exports (L loc b) = case b of
  AbsBinds { abs_exports, abs_binds } ->
    let subbinds = mconcat $ bagToList $ mapBag (bind_to_table with_abs_exports) abs_binds -- consider making union_sym_table just Foldable t => ...
    in if length subbinds > 0 && with_abs_exports
      then subbinds <> map (L loc . VarPat NoExt . noLoc . abe_poly &&& pure . sa_from_sym . Sym . L loc . HsVar NoExt . noLoc . abe_mono) abs_exports
      else subbinds
    
  -- AbsBindsSig { abs_sig_export, abs_sig_bind = L _ abs_sig_bind } -> 
  --   let subbinds = bind_to_table stack abs_sig_bind
  --   in subbinds {
  --       pms_syms = uncurry (insert abs_sig_export) $ (foldr (++) [] &&& id) $ pms_syms subbinds
  --     }
  
  -------------------
  -- SYM BASE CASE --
  -------------------
  FunBind { fun_id = fun_id, fun_matches } -> [( L loc (VarPat NoExt fun_id), [sa_from_sym (Sym $ (HsLam NoExt fun_matches <$ fun_id)) ])]
  
  PatBind { pat_lhs = pat_lhs, pat_rhs } ->
    (grhs_binds with_abs_exports) pat_rhs <> [(pat_lhs, map (sa_from_sym . Sym) (grhs_exprs pat_rhs))]
  VarBind {} -> mempty
  _ -> error $ constr_ppr b

-- gmapQ :: Data c => (forall d. Data d => d -> e) -> c -> [e]
-- uncurried: Data c => ((forall d. Data d => d -> e), c) -> [e]

grhs_binds :: Bool -> GenericQ [Bind] -- TODO consider passing more info via `GenericQ (Maybe PatMatchSyms)`, and removing the fromMaybe
grhs_binds with_abs_exports = go False where
  go :: Bool -> GenericQ [Bind]
  go is_do a =
    (
        concat (gmapQ (go is_do) a)
        `mkQ` (bind_to_table with_abs_exports)
        `extQ` (uncurry (++) . ((concat . gmapQ (go is_do)) &&& ((\case
            BindStmt _ pat expr _ _ ->
              let sa = sa_from_sym (Sym expr)
              in if is_do
                then [(pat, [sa {
                    sa_loc = StmtFrame : sa_loc sa
                  }])] -- TODO check if a fresh stack key here is the right thing to do
                else [(pat, [sa])]
            _ -> mempty
          ) :: Stmt GhcTc (LHsExpr GhcTc) -> [Bind]))) -- TODO dangerous: should we really keep looking deeper after finding a BindStmt?
        `extQ` ((\sym -> case sym of
          HsApp _ _ _ -> mempty
          HsLam _ _ -> mempty
          HsDo _ _ _ -> concat $ gmapQ (go True) sym
          _ -> concat $ gmapQ (go False) sym
        ) :: HsExpr GhcTc -> [Bind]) -- guard against applications and lambdas, which introduce bindings we need to dig into a scope to bind
      ) a

-- data TyComp = SUBTY | SUPERTY | NOCOMP

-- instance Applicative (GenLocated a) where
--   pure = L noLoc
--   (<*>) (L l f) = L l . fmap f