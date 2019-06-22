{-# LANGUAGE Rank2Types, NamedFieldPuns #-}

module Rahse (
	
) where
  import Functor
  import Data.Generics.Extra
  
  data DataFields = Args [[ReturnThing]] | Recs (Map Id [ReturnThing]) -- look at `HsConPatDetails` for the type of the record label name for the map key
  
  
	data ReturnThing =
		Var { rt_name :: Id } | -- we only need this because the Var might be bound to a pattern (or of course an imported value from a package)
		App { rt_left :: ReturnThing, rt_args :: [[ReturnThing]] } | -- App requires some help because resolving an argument might itself come from a function call. Note this includes data constructors
    List { rt_contents :: [ReturnThing] } | -- different from `App`: the arguments are in an unpredictable order
    Lit { rt_def :: HsLit } |
    Lam { rt_def :: MatchGroup Id (HsExpr Id) } -- needed because named function vars aren't 
    Case { rt_arg :: [ReturnThing], rt_def :: MatchGroup }
    
    -- Data { rt_fields :: DataFields } | -- omitting record args from v1
  
  type SymTable = Map Id (Maybe MatchGroup, [ReturnThing])
  
  -- at every step, I can go from an HsExpr to a ReturnThing along certain lines. Consider if a function exports both a lambda and a named function. Without thinking, I could flatten them here as if they were part of the same argument line even though I should be splitting, maybe doing the association here too while the return is not very ambiguous
  
  mg_cov_ids :: MatchGroup Id (HsExpr Id) -> [ReturnThing]
  mg_cov_ids = map (stmt_cov_ids . grhssGRHSs . m_grhss . unLoc) . unLoc . mg_alts
  -- stmt_cov_ids: oh man this one is annoying because of all the different kinds of statements; just pull bodies out wherever we can
  -- or actually I guess not
  
  stmt_cov_ids :: Stmt Id (HsExpr Id) -> [ReturnThing]
  stmt_cov_ids (BindStmt _ b _ _ _) = cov_ids b
  stmt_cov_ids (BodyStmt b _ _ _) = cov_ids b

  reduce_funs :: [ReturnThing] -> [ReturnThing]

	cov_ids :: HsExpr Id -> [ReturnThing] -- right-to-left unapplied covariant bindings
	cov_ids (HsVar l_id) = [Var $ unLoc l_id]
  cov_ids (HsLit lit) = [Lit lit]
	cov_ids (HsLam mg) = [Lam mg] -- it's annoying that this is possible because I then need to treat this like a function binding in the scope above this as a special case
  -- MatchGroup { mg_alts = L _ (L _ match })
  cov_ids (HsLamCase mg) = [Lam mg]
  cov_ids (HsCase arg mg) = [Case (cov_ids arg) mg] -- refactor as a function application with a pseudo unique name (which is easier said than done); do this when tying the knot so that this can stay simple with only ReturnThing (instead of making a map)
  cov_ids HsPar e = cov_ids e
  
  from_section :: HsExpr Id -> HsExpr Id -> [ReturnThing]
  from_section op arg = let args = cov_ids arg in
  cov_ids SectionL l op =
    let args = map 
    in map ((flip App) args
  cov_ids HsApp l r = l_app l $ [cov_ids $ unLoc r] where
    l_app :: HsExpr Id -> [[ReturnThing]] -> [ReturnThing]
    l_app expr@(HsApp _ _) = l_app expr . (cov_ids r):
    l_app expr args = cov_ids expr & map $ \l_ret -> case l_ret of
      App { rt_left, rt_args } -> App rt_left (rt_args ++ args)
      _ -> App l_ret args
      
      -- Some obsolete `data` handling:
      -- Var { rt_name } | isUpper $ head rt_name -> Data l_ret args
      -- Data { rt_fields = Args l_args } -> Data { rt_fields = (Args $ l_args ++ args) }
      -- Data { rt_fields = Recs l_recs } -> undefined -- doesn't make sense in an App; it'll be a runtime error -- Data { rt_fields = (Recs $ ) }
  cov_ids HsAppType l _ = cov_ids l -- ignore type apps for now; these will eventually make a difference
  cov_ids RecordCon{} = error "Record syntax yet to be implemented"
  cov_ids RecordUpd{} = error "Record syntax yet to be implemented"
  
  -- want to have something that goes ReturnThing -> [ReturnThing] for all the traversals, but sometimes the computation terminates with action on the ReturnThing. I just assume that the state of the pattern bindings from the arguments (e.g. in case, Lambda and Fun) will be temporary for a single level down, but for a lambda navigating within might pull free variables bound from the scopes outside, so unless I perform a beta reduction right there and convert it to another structure, I'll need to also have a structure to deal with that that persists in the arguments. That being said, the first map of bindings can be resolved right at the outset, so the map can be passed into lower scopes.
  
  tie :: SymTable -> [ReturnThing] -> (SymTable, [ReturnThing])
  -- generally wanting to make a state machine out of this means having a single-step function returning the list of the next destination, then recursive elements to take this single step and fix it with a state machine.
  tie table v@(Var{}) = (table, v)
  tie table App{ rt_left, rt_args } = case rt_left of
    Var{ rt_name } -> (
      case lookup rt_name table of
        Just (args, rts) -> map rts case args of -- rts from the return position of the function might need to be 
          
        Nothing -> undefined,
      
    )
  
  nameString :: Name -> String
  nameString = occNameString . nameOccName
  
  pat_match :: MatchGroup Id (HsExpr Id) -> [[ReturnThing]] -> SymTable
  -- foreach variable, foreach match for the function, pattern match by traversing the patterns, producing a map of each
  -- invariant: the length of the ReturnThing is the same arity as the length of the matchgroup, where the matchgroup arity is also uniform by algorithmic design
  -- 1d: all alternatives, 2d: each argument set, 3d: each value decomposition of each argument if there is a match (filtered; possibly empty Map)
  -- desired: compress all alternatives, make a list of value decompositions for each argument set (so transpose and concat)
  pat_match MatchGroup{ mg_alts } args = map unions $ transpose $ map (map (pat_match' . unLoc) . zip args . m_pats . unLoc . m_pats) mg_alts where -- refactor; there has to be a more elegant way to deal with these dimensions
    pat_match' :: ReturnThing -> Pat Id -> Maybe SymTable
    -- wrapping patterns
    pat_match' ret (ParPat (L _ pat)) = pat_match' ret pat
    pat_match' ret (BangPat (L _ pat)) = pat_match' ret pat
    
    -- var bindings
    pat_match' ret (VarPat (L _ id)) = Just $ singleton id ret
    pat_match' ret (AsPat (L _ id) (L _ pat)) = insert id ret <$> pat_match' ret pat
    
    -- data constructors
    pat_match' (App{ rt_left, rt_args }) (ConPatOut{ pat_con, pat_args }) =
      let con_name :: String
          con_name = case pat_con of
            RealDataCon con -> nameString $ dataConName con
            PatSyn con -> nameString $ patSynName con
          decompose :: [LPat Id] -> Maybe SymTable
          decompose = foldl1 (liftA2 union) . map (uncurry pat_match') . zip rt_args . map unLoc
      in if con_name == nameString $ varName $ rt_name rt_left -- narrowing
         then case pat_args of
           PrefixCon args -> decompose args -- foldl (\a x -> liftA2 union a $ uncurry pat_match' x) (Just empty) (zip vals args)
           RecCon _ -> error "Record syntax yet to be implemented"
           -- RecCon HsRecFields{ rec_flds } -> decompose $ map (hsRecFieldArg . unLoc) rec_flds -- assuming the typechecker sorts the fields in order of application, else we have to consult the definition
           -- never mind, the typechecker doesn't re-order so I do have to figure out the argument order somehow
         else Nothing
    pat_match' _ (ConPatOut{}) = Nothing
          
  
  data PatThing =
    CasePat HsExpr Match |
    FunPat 
  
  con_ids :: HsExpr -> []