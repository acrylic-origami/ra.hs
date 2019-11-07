{-# LANGUAGE LambdaCase, NamedFieldPuns #-}
module Plugin (frontendPlugin) where
  import System.Environment ( getArgs )
  -- import System.Console.GetOpt ( getOpt )
  
  import GHC
  import GhcPlugins
  import DriverPhases
  import GhcMonad
  import Var ( Var, varUnique )
  import Unique ( getUnique )
  import Bag ( bagToList )
  import qualified Data.Map.Strict as M
  import Data.Map.Strict ( Map(..), unionsWith, keys, toList, insert, insertWith )
  import Data.Generics ( cast, mkT, mkQ, extQ, everything, everywhere, everywhereBut, toConstr, Data(..) )
  import Data.Generics.Extra ( constr_ppr, shallowest, everything_ppr )
  import qualified Data.Map.Strict as M ( empty, elems )
  import Control.Arrow ( first, (&&&), (***) )
  import Data.List ( intersperse )
  import Data.Maybe ( fromMaybe, catMaybes )
  import Control.Monad ( mzero )
  
  import Ra ( pat_match, reduce, reduce_deep )
  import Ra.GHC ( bind_to_table, grhs_binds, varString )
  import Ra.Lang -- ( SymTable, Sym(..), SymApp(..), Stack(..), unSB, Stack(..), ReduceSyms(..), PatMatchSyms(..), Write(..) )
  import Ra.Lang.Extra

  import Outputable ( Outputable, interppSP, showSDocUnsafe, showPpr )
  
  frontendPlugin :: FrontendPlugin
  frontendPlugin = defaultFrontendPlugin {
    frontend = fe
  }
  
  fe :: [String] -> [(String, Maybe Phase)] -> Ghc ()
  fe flags args = do
    target <- guessTarget ("target/H.hs") Nothing
    setTargets [target] 
    load LoadAllTargets

    -- deps <- depanal [] False
    -- return $ show $ foldr ((:) . moduleNameString . moduleName . ms_mod) [] deps
    
    modSum <- getModSummary $ mkModuleName "H"
    p <- parseModule modSum
    t <- typecheckModule p
    
    let st0 = SB []
        initial_pms = pat_match $ grhs_binds (typecheckedSource t)
        syms0 = pms2rs initial_pms -- (\s -> s { sa_stack = append_frame (AppFrame s (pms_syms initial_pms)) (sa_stack s) }) $ head $ (!!0) $ M.elems $ 
        -- syms1 = everywhere (mkT (\sa -> sa {
        --     sa_stack = mapSB ((AppFrame (sa_from_sym EntryPoint) (pms_syms initial_pms)): ) (sa_stack sa)
        --   })) syms0 -- this makes it work, but feels verrrrry sketchy modifying stacks like that; it's almost like duplicating and tacking onto this "layer"
        rsn = reduce syms0
        ppr_final_writes :: Map StackKey [SymApp] -> String
        ppr_final_writes = concat . intersperse "\n===\n" . map ((
            uncurry ((++) . (++" -> "))
            . (
                ppr_unsafe
                *** concat . intersperse "\n" . map (ppr_sa (ppr_unsafe))
            )
          )) . M.assocs
        
        final_writes :: Map StackKey [SymApp]
        final_writes = foldr (flip (foldr ($))
          . uncurry (flip (map . ($))) -- [Map StackKey [SymApp] -> Map StackKey [SymApp]]
          . (
            map (\sa -> case sa_sym sa of
                Sym (L _ (HsVar _ v)) | (varString $ unLoc v) == "newEmptyMVar" -> Just $ make_stack_key sa
                _ -> Nothing
              ) -- [StackKey]
            *** (\v m_k -> case m_k of
                Just k -> insertWith (++) k v
                Nothing -> id
              ) -- [StackKey -> Map StackKey [SymApp] -> Map StackKey [SymApp]]
            -- map (((fromMaybe id).) . fmap . flip insert) -- sometimes pointfree isn't worth it
          )) mempty (concatMap rs_writes rsn)
    
    liftIO $ putStrLn $ ppr_final_writes final_writes
    -- liftIO $ putStrLn $ uncurry (++) $ (ppr_unsafe &&& show . length . fst . splitFunTys . varType) $ unLoc $ fun_id $ unLoc $ head $ bagToList $ abs_binds $ unLoc $ (!!2) $ bagToList $ typecheckedSource t
    -- liftIO $ putStrLn $ constr_ppr $ head $ bagToList $ typecheckedSource t
    -- return $ show $ length $ mconcat $ map rs_writes rsn
    -- return $ uncurry (++) . (show *** ppr_rs (ppr_unsafe)) $ reduce $ (!!1) $ catMaybes $ map (\b -> case unLoc b of { AbsBinds {} -> Just $ snd $ head $ bind_to_table st0 (unLoc b); _ -> Nothing }) $ bagToList (typecheckedSource t)
    -- return $ ppr_rs (ppr_unsafe) syms0
    
    -- return $ concatMap ((++"\n") . uncurry ((++) . (++" -> ")) . (ppr_unsafe *** concatMap (ppr_stack (ppr_unsafe) . sa_stack))) $ M.assocs $ stbl_table (pms_syms initial_pms)
    -- return $ ppr_pms (ppr_unsafe) initial_pms
    -- return $ concatMap (uncurry (++) . ((ppr_unsafe) *** (concatMap (ppr_sa (ppr_unsafe))))) $ grhs_binds (typecheckedSource t)
    -- return $ constr_ppr $ typecheckedSource t
