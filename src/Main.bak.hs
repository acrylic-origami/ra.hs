module Main where
import Control.Monad.IO.Class
import Util
import GHC
import GHC.Paths (libdir)
import Data.Generics
main :: IO ()
main = runGhc (Just libdir) $ do
  dflags <- getSessionDynFlags
  _ <- setSessionDynFlags dflags
  target <- guessTarget "/Users/derek-lam/dev/sandbox/2019-05-03-0/src/A.hs" Nothing
  setTargets [target]
  loaded <- load LoadAllTargets 
  case loaded of
    Succeeded -> do
      binds <- (getModSummary $ mkModuleName "A") >>= parseModule >>= typecheckModule >>= desugarModule >>= (return . mg_binds . dm_core_module)
      
      exprs <- return $ everything (++) ([] `mkQ` (singleton :: HsExpr GhcTc -> [HsExpr GhcTc])) (tm_typechecked_source tc_module)
      return ()
    _ -> return ()