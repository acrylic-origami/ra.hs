{-# LANGUAGE Rank2Types, LambdaCase, NamedFieldPuns, DeriveFunctor #-}

module Ra.Lang.Extra (
  ppr_unsafe,
  ppr_sa,
  ppr_rs,
  ppr_pms,
  ppr_stack,
  ppr_table,
  ppr_binds,
  -- ppr_writes
  tree_sa,
  Tree2(..)
) where

import GHC ( LHsExpr, GhcTc )
import Data.List ( intersperse )
import Data.Bool ( bool )
import Data.Maybe ( fromMaybe )
import Control.Arrow ( (&&&), (***) )
import Data.Tree ( Tree(..), Forest )

import Ra.Lang

import Outputable ( Outputable(..), showPpr, interppSP, showSDocUnsafe )
import Data.Map.Strict ( assocs )
import qualified Data.Map.Strict as M ( map, elems, assocs )

type Printer = (forall o. Outputable o => o -> String)

newtype Tree2 a = Tree2 (a, [[Tree2 a]]) deriving Functor

tree_sa :: Printer -> SymApp Sym -> Tree2 (StackKey, String)
tree_sa show' = go 0 where
  go :: Int -> SymApp Sym -> Tree2 (StackKey, String)
  go n = Tree2 . (
      (make_loc_key &&& show' . sa_sym) &&&
      map (map (go (n+1))) . sa_args
    )

ppr_sa :: Printer -> SymApp Sym -> String
ppr_sa show' = go 0 where
  go :: Int -> SymApp Sym -> String
  go n = 
    let indent = (replicate n ' ')
    in  (++(indent ++ ">"))
         . (
          uncurry (++)
          . (
              uncurry (++) . (
                  bool "" "*" . not . null . sa_consumers
                  &&& ((indent ++ "<")++) . (show' . sa_sym)
                )
              &&& uncurry (++) . (
                  concatMap (
                      (++("\n" ++ indent ++ " )\n"))
                      . (("\n" ++ indent ++ " (\n")++)
                      . concatMap (go (n+1))
                    ) . sa_args
                  &&& uncurry (++) . (
                      show' . make_loc_key
                      &&& uncurry (++) . (
                          fromMaybe "BASE" . fmap (show' . make_loc_key) . sa_thread
                          &&& show . sa_is_monadic
                        )
                    )
                )
            )
          )

-- ppr_writes :: Printer -> Writes -> String
-- ppr_writes show' = concatMap ((++"\n---\n") . uncurry ((++) . (++" -> ")) . (both $ concatMap ((++"\n") . ppr_sa show'))) where
--   both f = (f *** f)

-- ppr_hold :: Printer -> Hold -> String
-- ppr_hold show' = uncurry ((++) . (++" <- ")) . (show' . h_pat &&& ppr_sa show' . h_sym)

ppr_rs :: Printer -> ReduceSyms -> String
ppr_rs show' = flip concatMap printers . (("\n===\n"++).) . flip ($) where
  printers = [
      concatMap ((++"\n") . ppr_sa show') . rs_syms
      , concatMap ((++"\n") . ppr_sa show') . rs_stmts
    ]

ppr_pms :: Printer -> PatMatchSyms -> String
ppr_pms show' = flip concatMap printers . (("\n===\n"++).) . flip ($) where
  printers = [
      concatMap ((++"\n") . uncurry ((++) . (++" -> ")) . (show' *** concatMap ((++"\n") . ppr_sa show'))) . assocs . stbl_table . pms_syms
      , concatMap ((++"\n") . uncurry ((++) . (++" -> ")) . (show' *** concatMap (ppr_sa show'))) . stbl_binds . pms_syms
      , concatMap ((++"\n") . ppr_sa show') . pms_stmts
    ]

-- ppr_stack :: Printer -> Stack -> String
-- ppr_stack show' =
--   show . map (\case
--       AppFrame { af_syms, af_raw } ->
--         ppr_sa show' af_raw
--         ++ ", "
--         ++ (show $ map (
--             uncurry ((++) . (++" -> ")) . (
--                 show'
--                 *** concat . intersperse "\n" . map (ppr_sa show')
--               )
--           ) (M.assocs $ stbl_table af_syms))
--       VarRefFrame v -> show' v
--     )

ppr_binds :: Printer -> [Bind] -> String
ppr_binds show' = unlines . map (uncurry (++) . ((++" -> ") . show' *** concat . intersperse ", " . map (ppr_sa show')))

ppr_table :: Printer -> SymTable -> String
ppr_table show' = uncurry (++) . (
    foldr ((++) . (++"\n\n") . uncurry (++) . (((++", ") . show') *** concatMap (show' . sa_sym))) "" . M.assocs . stbl_table
    &&& ppr_binds show' . stbl_binds
  )

ppr_stack :: Printer -> Stack -> String
ppr_stack show' = foldr (\case
    AppFrame sa syms -> (++("---\n\nAF\n" ++ ppr_table show' syms))
    -- BindFrame syms -> (++("---\n\nBF\n" ++ ppr_table show' syms))
    BindFrame {} -> (++"---\n\nBF\n")
    
    _ -> id
  ) ""

ppr_unsafe :: Outputable a => a -> String
ppr_unsafe = showSDocUnsafe . interppSP . pure