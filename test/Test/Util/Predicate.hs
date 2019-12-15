module Test.Util.Predicate (
  any_result_match,
  all_result_match,
  lift_sa_eq
) where

import Control.Monad ( void )

import Test.Framework.Providers.HUnit
import Test.HUnit

import Test.Util.Lang

import Ra.Lang
import Ra.Lang.Extra

any_result_match = result_match or
all_result_match = result_match and

result_match ::
  ([Bool] -> Bool) -- results folder
  -> ([Bool] -> Bool) -- args folder
  -> [SymApp String] -> ReduceSyms -> IO ()
result_match res_fold arg_fold expects rs = do
  let syms' = str_syms $ rs_syms rs
  assertBool ("Matches failed" ++ ppr_rs ppr_unsafe rs) $ res_fold $ map (flip any expects . lift_sa_eq arg_fold (==)) syms'



lift_sa_eq ::
  ([Bool] -> Bool) -- args folder
  -> (a -> a -> Bool) -- liftee
  -> SymApp a -> SymApp a -> Bool
lift_sa_eq arg_fold f l r =
  length (sa_args l) == length (sa_args r)
  && f (sa_sym l) (sa_sym r)
  && all (\(ls', rs') -> arg_fold [lift_sa_eq arg_fold f l' r' | l' <- ls', r' <- rs']) (zip (sa_args l) (sa_args r))