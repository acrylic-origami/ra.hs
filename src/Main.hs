{-# LANGUAGE NamedFieldPuns #-}
module Main where
  import GHC
  import qualified Data.Map.Strict as Map
  import Outputable
  -- import GHC.Paths (libdir)

  cs :: TypecheckedModule -> Map Id Id
  ts :: TypecheckedModule -> Map Id Id

  -- consider the fact that there does need to be an accessory map of arguments where all of the expressions that are dependent on the argument map to the binding in that argument, so that invokations of the method can be tied to those arguments. Where will this list live? It's a specification of the otherwise single value -> single value, where we now have to ask: does that value have arguments, or is it a single value? This is only in the contravariant case, representing some lexical assymmetry because the return type is always there, but we have an argument type with zero or more type variables. There is an assymmetry anyways, since only the functions can accept values; every name comes with an argument list so we can bind the arguments to their supplied values when we need to. The only problem is that this needs to be a separate step, because the function call site doesn't have the names of the arguments if we haven't crawled it yet. Argh; maybe I should read that GHC article about tying the knot. This is a very imperative solution.
  -- I'll just try to find all the function bindings first; it seems necessary. This includes the nested bindings; I'll use SYB to be lazy 

  data ArgRef = A {
    fun :: Id,
    pos :: Int
  }
  data Source = Named Id | Arg ArgRef

  bound_to :: TypecheckedModule -> Map Id [Source]
  bound_to = everything union (empty `mkQ` bind_mapper) where
    bind_mapper :: HsBind -> Map Id [Source]
    bind_mapper b@FunBind { fun_id = L fun_id_, fun_matches = MatchGroup { mg_alts = L mg_alts_ } } =
      (singleton fun_id_ (cov_expr_mapper b)) `union`
      (con_expr_mapper b) `union`
      (foldl (union . snd . foldl arg_folder (0, empty) . m_pats) empty mg_alts_) where
        arg_folder :: (Int, Map Id [Source]) -> LPat -> (Int, Map Id [Source])
        arg_folder (m, i) (L pat) = -- new argument with pattern (m :: LPat)
          let source = (Arg (A fun_id_ i))
          in (i + 1, foldl ((flip (insert source)) m) empty (pat_mapper pat))
    bind_mapper VarBind { var_id, var_rhs = L expr } = singleton var_id (cov_mapper expr)
    bind_mapper = const empty
    
    pat_mapper :: HsPat -> [Id]
    pat_mapper = everything (++) ([] `mkQ` (id :: Id -> Id))
    
    cov_mapper :: HsBind -> Id -> Map Id [Source]
    cov_mapper = everything (++) ([] `mkQ` expr_mapper)
    
    cov_expr_mapper :: HsExpr -> [Id] -- create bindings for decomposing expressions and seek returning values
    cov_expr_mapper (HsVar v) = v
    -- cov_expr_mapper (HsOverLit) -- TODO
    cov_expr_mapper (HsLam MG) = mg_alts_mapper MG
    cov_expr_mapper (HsLamCase MG) = mg_alts_mapper MG
    cov_expr_mapper (HsApp (L ))
    cov_expr_mapper = const []
    
    mg_mapper (MatchGroup { mg_alts = L mg_alts_ }) = foldl ((unLoc & m_grhss & grhssGRHSs & foldl (\(L _ id) -> cov_expr_mapper id) []) . (++)) [] mg_alts_

  map_tl_binds :: (LHsBind -> Map a b) -> TypecheckedModule ->  Map a b
  map_tl_binds mapper = t & typecheckedModule & foldBag (\a x -> union a (mapper $ unLoc x)) empty -- the point-free version of the reducer is too annoying: it's `second (unLoc & mapper) & uncurry union & curry`

  type FunDeps = Map Id [[Id]]
  fun_deps :: TypecheckedModule -> FunDeps -- next idea: instead of just the top-level binds, SYB and compress into just the function bind case and the value bind to lambda case: the only ways to define argumented things (functions) here
  fun_deps = map_tl_binds mapper where
    mapper :: HsBind Id -> FunDeps
    mapper FunBind { fun_id, fun_matches } = insertMap fun_id (fun_bind_deps fun_matches) empty
    mapper 
    mapper = empty

    expr_deps :: HsBind Id -> FunDeps
    expr_deps = everything union (empty `mkQ` expr_bind_deps)

    expr_bind_deps :: HsLocalBind Id -> FunDeps
    expr_bind_deps 

    fun_bind_deps :: HsBind Id -> [[Id]]
    fun_bind_deps = mg_alts &
        unLoc &
        map (m_pats & id_q) &
        transpose

    id_q = everything (++) ([] `mkQ` (id :: Id -> Id))

  -- not the cleanest way to make this happen tbh, but whatever
  data BindDep = BindDep {
    dep :: Id,
    ctx :: HSExpr
  }
  type BindDeps = Map Id [BindDep]
  bind_deps :: TypecheckedModule -> FunDeps -> BindDeps
  bind_deps = map_tl_binds mapper where
    mapper :: LHsBind -> BindDeps
    mapper m FunBind { fun_matches, fun_id } = 

    q_fun m = m & m_pats & everything (++) ([] `mkQ` (id :: Id -> Id))
  -- first, I need to go from a set of expressions to ones that mention a consumer, then rescan the whole source to find where they're used. This may happen an arbitrary number of times which is unacceptable; instead I need to build a graph of all instances of uniques and the uniques that they are then mapped to. Note that this can be mutually recursive in general, e.g. bindings in a `let`. It's okay though, I'm just building equivalence classes. `Map Unique (Maybe Unique)` for a disjoint set. Note that at each expression we'll need to dive into it and pick up those bindings.
  data CA = CA {
    -- values that mention a consumer type
  }

  -- return all instances of expressions in variables and their binding uniques
  -- we need to find a function that returns a function body given a name, or else the recursion is dead: I need more than a type here because I need to know if the function pushes values elsewhere
  cs t = t & typecheckedSource & foldlBag z where
    z m b = case b of
      FunBind { fun_ext, fun_id, fun_matches } = ()
  -- ps :: TypecheckedModule -> Map Unique Unique
  type ps_track = Map Unique (Map Unique (Bool Bool))

  main :: IO ()
  main = do
    runGhc (Just libdir) $ do
      getSessionDynFlags >>= setSessionDynFlags
      target <- guessTarget "target/A.hs" Nothing
      setTargets [target] 
      load LoadAllTargets

      getModuleGraph >>= 

      modSum <- getModSummary $ mkModuleName "A"
      p <- parseModule modSum
      t <- typecheckModule p
      getBindings >>= 
      -- t & typecheckedSource & mapBag (fun_matches & )
      return ()