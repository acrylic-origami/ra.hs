{-# LANGUAGE Rank2Types, LambdaCase, TupleSections, NamedFieldPuns #-}
module Ra.GHC.Translate (
  grhs_binds,
  bind_to_table,
) where

import GHC
import Bag ( bagToList, mapBag )

import Data.Generics ( GenericQ, mkQ, extQ, everythingBut)
import Data.Generics.Extra ( shallowest, constr_ppr )
import Control.Arrow ( (&&&) )

import Ra.Lang -- ( Stack(..), SymApp(..), Sym(..), SymTable(..), PatMatchSyms(..), ReduceSyms(..), Stack(..), unSB, mapSB, union_sym_tables, make_loc_key )
import Ra.GHC.Util ( grhs_exprs )
import Ra.Extra

bind_to_table :: LHsBind GhcTc -> [Bind]
bind_to_table (L loc b) = case b of
  AbsBinds { abs_exports, abs_binds } ->
    let subbinds = mconcat $ bagToList $ mapBag bind_to_table abs_binds -- consider making union_sym_table just Foldable t => ...
    in subbinds <> map (L loc . VarPat NoExt . noLoc . abe_poly &&& pure . sa_from_sym . Sym . L loc . HsVar NoExt . noLoc . abe_mono) abs_exports
    
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
    grhs_binds pat_rhs <> [(pat_lhs, map (sa_from_sym . Sym) (grhs_exprs pat_rhs))]
  VarBind {} -> mempty
  _ -> error $ constr_ppr b

-- gmapQ :: Data c => (forall d. Data d => d -> e) -> c -> [e]
-- uncurried: Data c => ((forall d. Data d => d -> e), c) -> [e]

grhs_binds :: GenericQ [Bind] -- TODO consider passing more info via `GenericQ (Maybe PatMatchSyms)`, and removing the fromMaybe
grhs_binds = everythingBut (<>) (
    (mempty, False)
    `mkQ` ((,True) . bind_to_table)
    `extQ` ((,False) . ((\case
        BindStmt _ pat expr _ _ -> [(pat, [sa_from_sym (Sym expr)])] -- TODO check if a fresh stack key here is the right thing to do
        _ -> mempty
      ) . unLoc :: LStmt GhcTc (LHsExpr GhcTc) -> [Bind])) -- TODO dangerous: should we really keep looking deeper after finding a BindStmt?
    `extQ` ((mempty,) . ((\case 
      HsApp _ _ _ -> True
      HsLam _ _ -> True
      _ -> False 
    ) :: HsExpr GhcTc -> Bool)) -- guard against applications and lambdas, which introduce bindings we need to dig into a scope to bind
  )

-- data TyComp = SUBTY | SUPERTY | NOCOMP

-- instance Applicative (GenLocated a) where
--   pure = L noLoc
--   (<*>) (L l f) = L l . fmap f