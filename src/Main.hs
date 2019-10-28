{-# LANGUAGE LambdaCase, NamedFieldPuns #-}
module Main where
  import System.Environment ( getArgs )
  -- import System.Console.GetOpt ( getOpt )
  
  import GHC
  import GHC.Paths ( libdir )
  import Var ( Var, varUnique )
  import Unique ( getUnique )
  import Bag ( bagToList )
  import qualified Data.Map.Strict as M
  import Data.Map.Strict ( unionsWith, keys, toList )
  import Data.Generics ( cast, mkQ, extQ, everything, toConstr, Data(..) )
  import Data.Generics.Extra ( constr_ppr, shallowest, everything_ppr )
  import qualified Data.Map.Strict as M ( empty, elems )
  import Data.Tuple.Extra ( first, (&&&), (***) )
  import Data.Maybe ( fromMaybe )
  import Control.Monad ( mzero )
  
  import Ra ( pat_match, reduce, reduce_deep )
  import Ra.GHC ( bind_to_table, grhs_binds )
  import Ra.Lang -- ( SymTable, Sym(..), SymApp(..), StackBranch(..), unSB, Stack(..), ReduceSyms(..), PatMatchSyms(..), Write(..) )
  import Ra.Lang.Extra

  import Outputable ( Outputable, interppSP, showSDocUnsafe, showPpr )
  
  main :: IO ()
  main = do
    mod_str:_ <- getArgs
    (putStrLn=<<) $ runGhc (Just libdir) $ do
      dflags <- getSessionDynFlags
      setSessionDynFlags dflags
      target <- guessTarget ("target/" ++ mod_str ++ ".hs") Nothing
      setTargets [target] 
      load LoadAllTargets

      -- deps <- depanal [] False
      -- return $ show $ foldr ((:) . moduleNameString . moduleName . ms_mod) [] deps
      
      modSum <- getModSummary $ mkModuleName mod_str
      p <- parseModule modSum
      t <- typecheckModule p
      
      let st0 = Stack (SB []) (SB [], SB [])
          initial_pms = pat_match $ grhs_binds st0 (typecheckedSource t)
          syms0 = pms2rs initial_pms -- (\s -> s { sa_stack = append_frame (AppFrame s (pms_syms initial_pms)) (sa_stack s) }) $ head $ (!!0) $ M.elems $ 
      
      return $ uncurry (++) . (show *** ppr_rs (showPpr dflags)) $ reduce syms0
      -- return $ ppr_pms (showPpr dflags) initial_pms
      -- return $ constr_ppr $ typecheckedSource t
