{-# LANGUAGE LambdaCase, NamedFieldPuns #-}
module Main where
  import GHC
  import GHC.Paths ( libdir )
  import Var ( Var, varUnique )
  import Unique ( getUnique )
  import Bag ( bagToList )
  import qualified Data.Map.Strict as M
  import Data.Map.Strict ( unionsWith, keys, toList )
  import Data.Generics ( cast, mkQ, extQ, everything, toConstr, Data(..) )
  import Data.Generics.Extra ( constr_ppr, shallowest, everything_ppr )
  import qualified Data.Map.Strict as M ( empty )
  import Data.Tuple.Extra ( (&&&), (***) )
  
  import Ra ( pat_match, reduce_deep )
  import Ra.GHC ( bind_to_table )
  import Ra.Stack ( SymTable, Sym, StackBranch )

  import Outputable ( Outputable, interppSP, showSDocUnsafe, showPpr )

  ppr :: Outputable a => a -> String
  ppr = showSDocUnsafe . interppSP . pure
  
  ppr_branch :: StackBranch -> String
  ppr_branch = foldr ((++) . (++"---\n\n") . foldr ((++) . (++"\n\n") . uncurry (++) . (((++", ") . ppr) *** ppr)) "" . toList . snd) ""

  main :: IO ()
  main = (putStrLn=<<) $ runGhc (Just libdir) $ do
    dflags <- getSessionDynFlags
    setSessionDynFlags dflags
    target <- guessTarget "target/A.hs" Nothing
    setTargets [target] 
    load LoadAllTargets

    modSum <- getModSummary $ mkModuleName "A"
    p <- parseModule modSum
    t <- typecheckModule p
    
    -- _ <- mapM (putStrLn . show . constr_ppr) tl_binds
    -- return $ foldr ((++) . ('\n':) . showPpr dflags) "" tl_binds
    -- return $ foldr (\x -> (++((constr_ppr x ++ "\n" ++ showPpr dflags x ++ "\n---")))) "" tl_binds
    -- return $ show $ map (showPpr dflags) ((concat $ shallowest cast (last tl_binds)) :: [HsExpr Id]) -- ) []
    
    let tl_binds = bagToList (typecheckedSource t)
        initial_branch = [(noSrcSpan, unionsWith (++) $ map (bind_to_table ([(noSrcSpan, M.empty)]) . unLoc) tl_binds)]
    -- return $ show $ map (M.mapKeys ppr . M.map (map toConstr) . snd) initial_branch
    return $ show $ map (showPpr dflags) $ concatMap (reduce_deep initial_branch []) ((concat $ shallowest cast (last tl_binds)) :: [HsExpr Id])
    
    -- return $ show $ map (show_sym dflags) $ concatMap (flip (reduce_deep $ [(noSrcSpan, SymTable $ unionsWith (++) $ map (bind_to_table ([(noSrcSpan, SymTable M.empty)]) . unLoc) $ bagToList (typecheckedSource t))]) []) ((concat $ shallowest cast (last $ bagToList (typecheckedSource t))) :: [HsExpr Id])
    
    -- return $ concat $ everything (++) ([] `mkQ` ((\b -> case b of
    --     FunBind{ fun_id } -> [(show $ varUnique $ unLoc fun_id) ++ " | " ++ (showPpr dflags b) ++ "\n"]
    --     VarBind{ var_id } -> [(show $ varUnique var_id) ++ " | " ++ (showPpr dflags b) ++ "\n"]
    --     _ -> []
    --   ) :: HsBind Id -> [String])) tl_binds
    
    -- return $ foldr1 ((++) . ('\n':)) $ map (\x -> (show $ getUnique x) ++ " | " ++ (showPpr dflags x)) $ (everything (++) ([] `mkQ` ((pure . id) :: Id -> [Id])) tl_binds)
    -- return $
      -- everything_ppr ((show . toConstr) `extQ` ((uncurry ((++) . (++" | ")) . (showPpr dflags &&& show . getUnique)) :: Id -> String)) tl_binds
    --   ++ "\n"
    --   ++ (everything (++) ([] `mkQ` ((\expr -> case expr of { (HsVar (L _ v)) -> (showPpr dflags expr ++ " | " ++ (show $ varUnique v)) ++ "\n"; _ -> "" }))) $ concatMap (reduce_deep initial_branch []) ((concat $ shallowest cast (last tl_binds)) :: [HsExpr Id]))
      
    -- return $ show $ map (showPpr dflags) tl_binds
    -- return $ constr_ppr $ typecheckedSource t
    -- return $ constr_ppr $ head $ ((concat $ shallowest cast (last tl_binds)) :: [HsExpr Id])
    
    -- let initial_branch = [()]
    -- initial_table = bind_to_table [(empty, (typecheckedSource t))] -- BOOKMARK do this tomorrow
    -- t & typecheckedSource & mapBag (fun_matches & )
    