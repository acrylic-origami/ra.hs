{-# LANGUAGE LambdaCase, NamedFieldPuns #-}
module Main where
  import System.Environment ( getArgs )
  -- import System.Console.GetOpt ( getOpt )
  
  import DynFlags
  import GHC
  import SrcLoc ( srcSpanFileName_maybe )
  import FastString ( mkFastString )
  import Digraph ( flattenSCC )
  import Class ( Class(..) )
  import GHC.Paths ( libdir )
  import Var ( Var, varUnique, varType )
  import Type ( getTyVar_maybe, tyConAppTyCon_maybe )
  import TyCon ( tyConName, tyConTyVars, tyConStupidTheta, tyConName )
  import ConLike ( ConLike(..) )
  import DataCon ( dataConName, DataCon )
  import Name ( nameOccName, nameUnique )
  import OccName ( occNameString )
  import Unique ( getUnique, Unique(..) )
  import Bag ( bagToList )
  import qualified Data.Map.Strict as M
  import Data.Map.Strict ( Map(..), unionsWith, keys, toList, insert, insertWith )
  import Data.Generics ( cast, mkT, mkQ, extQ, everything, everywhere, everywhereBut, toConstr, Data(..) )
  import Data.Generics.Extra ( constr_ppr, shallowest, everything_ppr )
  import qualified Data.Map.Strict as M ( empty, elems )
  import Control.Arrow ( first, second, (&&&), (***) )
  import Data.List ( intersperse )
  import Data.Function ( fix )
  import Data.Maybe ( fromMaybe, catMaybes, listToMaybe )
  import Control.Monad ( mzero )
  import Control.Monad.IO.Class ( liftIO )
  
  import Ra ( or_pat_match_many, pat_match, reduce_deep )
  import Ra.Impure ( reduce )
  import Ra.GHC.Translate ( bind_to_table, grhs_binds )
  import Ra.GHC.Util ( varString )
  import Ra.Lang -- ( SymTable, Sym(..), SymApp(..), Stack(..), unSB, Stack(..), ReduceSyms(..), PatMatchSyms(..), Write(..) )
  import Ra.Lang.Extra
  
  import Outputable ( Outputable, interppSP, showSDocUnsafe, showPpr )

  module_binds :: GhcMonad m => ModSummary -> m [Bind]
  module_binds ms = (parseModule ms >>= typecheckModule) >>= (return . (grhs_binds True) . typecheckedSource)
  
  constr_var_ppr :: Data d => d -> String
  constr_var_ppr = everything_ppr ((show . toConstr) `extQ` (uncurry ((++) . (++" : ")) . (varString &&& show . varUnique)))
  
  {-
    let st0 = SB []
        initial_pms = pat_match $ typecheckedSource t
        -- syms0 = pms2rs initial_pms -- (\s -> s { sa_stack = append_frame (AppFrame s (pms_syms initial_pms)) (sa_stack s) }) $ head $ (!!0) $ M.elems $ 
        -- syms1 = everywhere (mkT (\sa -> sa {
        --     sa_stack = mapSB ((AppFrame (sa_from_sym EntryPoint) (pms_syms initial_pms)): ) (sa_stack sa)
        --   })) syms0 -- this makes it work, but feels verrrrry sketchy modifying stacks like that; it's almost like duplicating and tacking onto this "layer"
        rsn = M.map $ pms_syms $ pat_match reduce 
        -- rsn = reduce syms0
        ppr_final_writes :: Map StackKey [SymApp] -> String
        ppr_final_writes = concat . intersperse "\n===\n" . map ((
            uncurry ((++) . (++" -> "))
            . (
                showPpr dflags
                *** concat . intersperse "\n" . map (ppr_sa (showPpr dflags))
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
    
    -- return $ ppr_final_writes final_writes
        -- uncurry (++) $ (ppr_unsafe &&& show . length . fst . splitFunTys . varType)
    -- return $ constr_ppr $ varType $ unLoc $ fun_id $ unLoc $ head $ bagToList $ abs_binds $ unLoc $ (!!1) $ bagToList $ typecheckedSource t
    -- return $ concatMap (ppr_rs ppr_unsafe) rsn
    return (head rsn) {
        rs_syms = concatMap rs_syms rsn
      }
    -- let sr = fromMaybe [] . fmap (pure . ppr_unsafe . nameUnique . tyConName) . tyConAppTyCon_maybe
    -- return $ unlines $ everything (++) ([] `mkQ` ((\case
    --     HsVar _ (L _ v) -> everything (++) ([] `mkQ` sr) (varType v)
    --     -- HsConLikeOut _ (RealDataCon d) -> [occNameString $ nameOccName $ dataConName d]
    --     _ -> []
    --   ) :: HsExpr GhcTc -> [String]) `extQ` sr) (typecheckedSource t)
    -- return $ constr_ppr $ typecheckedSource t
    -- return $ everything (++) ("" `mkQ` (ppr_unsafe . tyConStupidTheta :: TyCon -> String)) (typecheckedSource t)
    -- return $ ppr_unsafe $ getTyVar "" $ varType $ head $ M.keys $ stbl_table $ pms_syms initial_pms
    -- return $ show $ length $ mconcat $ map rs_writes rsn
    -- return $ uncurry (++) . (show *** ppr_rs (showPpr dflags)) $ reduce $ (!!1) $ catMaybes $ map (\b -> case unLoc b of { AbsBinds {} -> Just $ snd $ head $ bind_to_table st0 (unLoc b); _ -> Nothing }) $ bagToList (typecheckedSource t)
    -- return $ ppr_rs (showPpr dflags) syms0
    
    -- return $ concatMap ((++"\n") . uncurry ((++) . (++" -> ")) . (showPpr dflags *** concatMap (ppr_stack (showPpr dflags) . sa_stack))) $ M.assocs $ stbl_table (pms_syms initial_pms)
    -- return $ ppr_pms (showPpr dflags) initial_pms
    -- return $ concatMap (uncurry (++) . ((showPpr dflags) *** (concatMap (ppr_sa (showPpr dflags))))) $ grhs_binds (typecheckedSource t)
    -- return $ constr_ppr $ typecheckedSource t -}

  main :: IO ()
  main = do
    mod_str:args' <- getArgs
    (putStrLn=<<) $ runGhc (Just libdir) $ do
      dflags <- getSessionDynFlags
      let inc_paths = includePaths dflags
      setSessionDynFlags $ dflags {
        includePaths = inc_paths {
          includePathsGlobal = "base/C/include/":(includePathsGlobal inc_paths)
          },
          importPaths = "target":"purebase/hiddens":"purebase/base/":"purebase/insts":(importPaths dflags)
          -- packageFlags = [ExposePackage "stm" (PackageArg "") (ModRenaming True [])]
        }
      -- importPaths = "purebase/hiddens":"purebase/base/":"purebase/insts":(importPaths dflags)
      target <- guessTarget ("target/" ++ mod_str ++ ".hs") Nothing
      setTargets [target] 
      load LoadAllTargets

      deps <- depanal [] False
      
      -- let n = fromMaybe 6 $ read <$> listToMaybe args'
      
      tl_binds <- mconcat <$> mapM module_binds (mgModSummaries deps)
      let tl_frame = BindFrame $ SymTable {
              stbl_table = fromMaybe mempty $ or_pat_match_many tl_binds,
              stbl_binds = tl_binds
            }
          tl_binds' = map (second (map (\sa -> sa { sa_stack = tl_frame : (sa_stack sa) }))) tl_binds
      -- mapM (\mss -> do
      --     binds <- mconcat <$> mapM module_binds mss
      --     liftIO $ putStrLn $ (concat $ intersperse ", " $ map (moduleNameString . moduleName . ms_mod) mss) ++ ":" ++ (show $ M.size $ stbl_table $ pms_syms $ pat_match binds)
      --   ) (fix (\t x -> case x of
      --       _:_ -> take n x : t (drop n x)
      --       [] -> []
      --     ) (mgModSummaries deps))
      
      -- return ""
      
      -- return $ show $ foldr ((:) . moduleNameString . moduleName . ms_mod) [] (mgModSummaries $ deps)
      
      let -- tl_pms = pat_match tl_binds'
          this_binds :: [Bind]
          this_binds = filter (fromMaybe False . fmap (==(mkFastString $ "target/" ++ mod_str ++ ".hs")) . srcSpanFileName_maybe . getLoc . fst) $ tl_binds' -- [[ReduceSyms]] -- map (uncurry (++) . ((++": ") . show . getLoc &&& ppr_unsafe) . fst) $ 
      
      -- return $ show $ length $ stbl_binds $ pms_syms tl_pms
      -- liftIO $ putStrLn $ everything_ppr ((show . toConstr) `extQ` (ppr_unsafe . (id &&& varUnique))) (tl_binds)
      -- liftIO $ putStrLn $ showPpr dflags $ everything (<>) ([] `mkQ` (pure . (id &&& varUnique))) $ tl_binds
      -- liftIO $ putStrLn $ showPpr dflags $ everything (<>) ([] `mkQ` ((\case
          -- (OpApp _ _ (L _ (HsWrap _ _ (HsVar _ v))) _) -> [(id &&& varUnique) $ unLoc v]
      --     _ -> []) :: HsExpr GhcTc -> [(Id, Unique)])) $ tl_binds
      -- return $ constr_var_ppr tl_binds
      return $ unlines $ map (ppr_sa (showPpr dflags)) $ rs_syms $ mconcat $ map (mconcat . map (head . reduce . flip ReduceSyms mempty . pure) . snd) this_binds
      
      -- liftIO (trySerialize tl_pms >>= deserialize >>= return . ppr_pms ppr_unsafe)
      
      -- return $ show $ length $ rs_syms tl_rs
      
      -- modSum <- getModSummary $ mkModuleName mod_str
      -- <- reduce_
