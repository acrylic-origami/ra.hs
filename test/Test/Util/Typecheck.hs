module Test.Util.Typecheck (
  ghc_setup,
  tc,
  tc_bind,
  tc_analyze,
  tc_test,
  tc_hang_test
) where
  
import GHC
import DynFlags
import GHC.Paths ( libdir )

import Data.Maybe ( fromMaybe )
import Control.Arrow ( (&&&), (***), first, second )
import Control.Monad.IO.Class ( liftIO )
import System.Timeout ( timeout )

import Test.Framework.Providers.HUnit
import Test.HUnit

import Test.Util.Lang

import Ra.GHC.Translate
import Ra ( or_pat_match_many )
import Ra.Impure ( reduce )
import Ra.Lang

max_time = floor 1E7

-- to refine: is this needed in every `tc`?
ghc_setup :: GhcMonad m => m ()
ghc_setup = do
  dflags <- getSessionDynFlags
  setSessionDynFlags dflags
  target <- guessTarget ("tmp/Test.hs") Nothing
  setTargets [target]

tc :: GhcMonad m => String -> m (TypecheckedModule)
tc pgm = do
  ghc_setup
  liftIO $ writeFile "tmp/Test.hs" ("module Test where\n" ++ pgm)
  load (LoadUpTo (mkModuleName "Test"))
  modSum <- getModSummary $ mkModuleName "Test"
  p <- parseModule modSum
  typecheckModule p

tc_bind :: GhcMonad m => String -> m [Bind]
tc_bind pgm = do
  ghc_setup
  tl_binds <- ((grhs_binds False) . typecheckedSource) <$> tc pgm
  let tl_frame = BindFrame $ SymTable {
          stbl_table = fromMaybe mempty $ or_pat_match_many tl_binds',
          stbl_binds = tl_binds'
        }
      tl_binds' = map (second (map (\sa -> sa { sa_stack = tl_frame : (sa_stack sa) }))) tl_binds
  return tl_binds'

analyze :: [Bind] -> ReduceSyms
analyze = mconcat . map (reduce . snd)

tc_analyze :: GhcMonad m => String -> m (Maybe ReduceSyms)
tc_analyze pgm = do
  ghc_setup
  binds <- tc_bind pgm
  liftIO $ timeout max_time (return $! analyze binds)

tc_hang_test :: GhcMonad m => String -> m ()
tc_hang_test pgm = tc_test pgm $ const $ return () -- putStrLn . unlines . map (ppr_sa ppr_unsafe) . rs_syms

tc_test :: GhcMonad m => String -> (ReduceSyms -> IO ()) -> m ()
tc_test pgm f = do
    ghc_setup
    rs <- tc_analyze pgm
    liftIO $ case rs of
      Just rs -> f rs
      Nothing -> assertFailure "Timeout"