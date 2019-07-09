{-# LANGUAGE NamedFieldPuns #-}
module Main where
  import GHC
  import GHC.Paths (libdir)
  import Data.Map.Strict
  import Outputable
  import Ra ( bind_to_table, pat_match, reduce_deep, reduce1 )

  main :: IO ()
  main = runGhc (Just libdir) $ do
      getSessionDynFlags >>= setSessionDynFlags
      target <- guessTarget "target/A.hs" Nothing
      setTargets [target] 
      load LoadAllTargets

      modSum <- getModSummary $ mkModuleName "A"
      p <- parseModule modSum
      t <- typecheckModule p
      -- let initial_branch = [()]
      -- initial_table = bind_to_table [(empty, (typecheckedSource t))] -- BOOKMARK do this tomorrow
      -- t & typecheckedSource & mapBag (fun_matches & )
      return ()