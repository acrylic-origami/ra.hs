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
  import Data.Tuple.Extra ( (&&&), (***) )
  import Control.Monad ( mzero )
  
  import Ra ( pat_match, reduce )
  import Ra.GHC ( bind_to_table )
  import Ra.Lang ( SymTable, Sym(..), SymApp(..), StackBranch(..), unSB, Stack(..), ReduceSyms(..), PatMatchSyms(..), Write(..) )
  import Ra.Lang.Extra

  import Outputable ( Outputable, interppSP, showSDocUnsafe, showPpr )

  ppr :: Outputable a => a -> String
  ppr = showSDocUnsafe . interppSP . pure
  
  ppr_branch :: StackBranch -> String
  ppr_branch = foldr ((++) . (++"---\n\n") . foldr ((++) . (++"\n\n") . uncurry (++) . (((++", ") . ppr) *** concatMap (ppr . sa_sym))) "" . toList . snd) "" . unSB

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
      
      -- _ <- mapM (putStrLn . show . constr_ppr) tl_binds
      -- return $ foldr ((++) . ('\n':) . showPpr dflags) "" tl_binds
      -- return $ foldr (\x -> (++((constr_ppr x ++ "\n" ++ showPpr dflags x ++ "\n---")))) "" tl_binds
      -- return $ show $ map (showPpr dflags) ((concat $ shallowest cast (last tl_binds)) :: [HsExpr GhcTc]) -- ) []
      
      let tl_binds = bagToList (typecheckedSource t)
          initial_pms = mconcat $ map (bind_to_table (mempty {
                st_branch = SB [(noSrcSpan, M.empty)]
              }) . unLoc) tl_binds
      -- return $ show $ map (M.mapKeys ppr . M.map (map toConstr) . snd) initial_branch
      -- pure ()
      -- return $ uncurry (++) $ (
      --     concatMap (
      --         (++"\n") . ppr_sa (showPpr dflags)
      --       )
      --     . rs_syms &&& concatMap (
      --       (++"\n")
      --       . ppr_sa (showPpr dflags)
      --       . w_sym)
      --     . concat
      --     . M.elems
      --     . rs_writes
      --   ) $ reduce initial_table $ (sa_sym $ head $ (!!1) $ M.elems $ initial_table)
      
      let rs = reduce (pms_syms initial_pms) $ (sa_sym $ head $ (!!1) $ M.elems $ (pms_syms initial_pms))
      -- return $ ppr_pms (showPpr dflags) initial_pms
      return $ ppr_rs (showPpr dflags) $ rs {
        rs_writes = M.unionWith (++) (pms_writes initial_pms) (rs_writes rs),
        rs_holds = pms_holds initial_pms <> rs_holds rs
      }
      -- return $ concatMap (uncurry ((++) . (++" -> ")) . (showPpr dflags *** concatMap (showPpr dflags . getLoc . (\(HsLam _ m) -> mg_alts m) . unLoc . sa_sym))) $ M.assocs $ pms_syms initial_pms
      
      -- return $ show $ map (show_sym dflags) $ concatMap (flip (reduce_deep $ [(noSrcSpan, SymTable $ unionsWith (++) $ map (bind_to_table ([(noSrcSpan, SymTable M.empty)]) . unLoc) $ bagToList (typecheckedSource t))]) []) ((concat $ shallowest cast (last $ bagToList (typecheckedSource t))) :: [HsExpr GhcTc])
      
      -- return $ concat $ everything (++) ([] `mkQ` ((\b -> case b of
      --     FunBind{ fun_id } -> [(show $ varUnique $ unLoc fun_id) ++ " | " ++ (showPpr dflags b) ++ "\n"]
      --     VarBind{ var_id } -> [(show $ varUnique var_id) ++ " | " ++ (showPpr dflags b) ++ "\n"]
      --     _ -> []
      --   ) :: HsBind GhcTc -> [String])) tl_binds
      
      -- return $ foldr1 ((++) . ('\n':)) $ map (\x -> (show $ getUnique x) ++ " | " ++ (showPpr dflags x)) $ (everything (++) ([] `mkQ` ((pure . id) :: Id -> [Id])) tl_binds)
      -- return $
        -- everything_ppr ((show . toConstr) `extQ` ((uncurry ((++) . (++" | ")) . (showPpr dflags &&& show . getUnique)) :: Id -> String)) tl_binds
      --   ++ "\n"
      --   ++ (everything (++) ([] `mkQ` ((\expr -> case expr of { (HsVar (L _ v)) -> (showPpr dflags expr ++ " | " ++ (show $ varUnique v)) ++ "\n"; _ -> "" }))) $ concatMap (reduce_deep initial_branch []) ((concat $ shallowest cast (last tl_binds)) :: [HsExpr GhcTc]))
        
      -- return $ show $ (\(L _ (AbsBinds{ abs_ev_binds })) -> map (showPpr dflags) abs_ev_binds) (last tl_binds)
      
      -- return $ show $ map (showPpr dflags) tl_binds
      -- return $ constr_ppr $ typecheckedSource t
      -- return $ constr_ppr $ head $ ((concat $ shallowest cast (last tl_binds)) :: [HsExpr GhcTc])
      
      -- let initial_branch = [()]
      -- initial_table = bind_to_table [(empty, (typecheckedSource t))] -- BOOKMARK do this tomorrow
      -- t & typecheckedSource & mapBag (fun_matches & )
      