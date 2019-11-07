import GHC.Paths
import System.Posix.Process
import System.Environment

main = do
  args <- getArgs
  let interactive = "--interactive" `elem` args
      args' = do
        arg <- args
        case arg of
          "--interactive" ->
            ["--frontend", "Main",
             "-plugin-package", "rahse"]
          _ -> return arg
  executeFile ghc False (args' ++ if interactive then ["-user-package-db"] else []) Nothing