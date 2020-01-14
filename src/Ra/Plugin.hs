{-# LANGUAGE LambdaCase #-}
module Ra.Plugin where

import GhcPlugins ( Plugin(..), impurePlugin, defaultPlugin, CommandLineOption, extractDynFlags )
import GHC.Paths ( libdir )
import GHC
import IOEnv
import HscTypes
import TcRnTypes
import Type
import SrcLoc ( srcSpanFileName_maybe )
import FastString ( unpackFS )
import Data.List ( isPrefixOf )
import Outputable ( Outputable(..), showPpr, interppSP, showSDocUnsafe )

import Data.Maybe
import Data.IORef
import System.IO.Unsafe
import Control.Monad
import Control.Arrow ( (&&&), (***), first, second )

import Data.Graph.Inductive.Graph ( pre, suc, lab, Graph(..) )
import Data.Generics ( Data, Typeable, mkQ, extQ, everything )

import Ra.GHC.Translate ( grhs_binds )
import Ra.Lang.Extra ( ppr_rs )
import Ra.Lang ( SymApp(..), Bind(..), ReduceSyms(..), SymTable(..), Sym(..), StackFrame(..), sa_from_sym )
import Ra ( or_pat_match_many )

import Ra.Plugin.CallGraph
import Paths_rahse ( getDataDir, getDataFileName )

plugin :: Plugin
plugin = defaultPlugin {
  typeCheckResultAction = install
  , pluginRecompile = impurePlugin
  }

r :: IORef [LHsBinds GhcTc]
r = unsafePerformIO $ newIORef []

ppr_unsafe :: Outputable a => a -> String
ppr_unsafe = showSDocUnsafe . interppSP . pure

module_binds :: GhcMonad m => ModSummary -> m [Bind]
module_binds = fmap ((grhs_binds False) . typecheckedSource) . module_tcs

module_tcs :: GhcMonad m => ModSummary -> m TypecheckedModule
module_tcs = (typecheckModule=<<) . parseModule

install :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
install opts _ms tc_gbl = do
  env <- getEnv
  let dflags = extractDynFlags env
  binds <- liftIO $ atomicModifyIORef r ((id &&& id) . (tcg_binds tc_gbl :))
  -- liftIO $ putStrLn $ show $ (length $ hsc_targets $ env_top env, length binds)
  when (length binds == (length $ hsc_targets $ env_top env)) $ liftIO $ do
    -- liftIO $ putStrLn $ unlines $ map ppr_unsafe $ everything (++) (mempty `mkQ` ((\case { HsDo xdo _ _ -> [xdo]; _ -> [] }) :: HsExpr GhcTc -> [Type])) binds
    
    datadir <- getDataDir
    fn <- getDataFileName "purebase/base/C/Union.hs"
    putStrLn fn
    pb_tl_binds <- runGhc (Just libdir) $ do
      dflags' <- getSessionDynFlags
      setSessionDynFlags dflags' {
        importPaths = (datadir ++ "/purebase/base") : (datadir ++ "/purebase/hiddens") : (datadir ++ "/purebase/insts") : importPaths dflags' 
      }
      target <- guessTarget "C.Union" Nothing
      setTargets [target]
      load LoadAllTargets
      deps <- depanal [] False
      mconcat <$> mapM module_binds (mgModSummaries deps)
    
    let tl_binds = pb_tl_binds ++ concatMap (grhs_binds False) binds
        tl_frame = BindFrame $ SymTable {
            stbl_table = fromMaybe mempty $ or_pat_match_many tl_binds',
            stbl_binds = tl_binds'
          }
        tl_binds' = map (second (map (\sa -> sa { sa_stack = tl_frame : (sa_stack sa) }))) tl_binds
        this_binds = filter (fromMaybe True . fmap (not . isPrefixOf datadir . unpackFS) . srcSpanFileName_maybe . getLoc . fst) tl_binds'
    putStrLn $ unlines $ map (("**--**\n"++) . ppr_rs (showPpr dflags)) $ reduce_all this_binds
    
  return tc_gbl