module Ra (
  Sym,
  SymTable,
  StackTable,
  StackBranch,
  bind_to_table,
  pat_match,
  reduce_deep,
  reduce1
) where
  import Data.Generics
  import Data.Generics.Extra
  import Data.Tuple.Extra (***)
  import Data.Function.Syntax (*.)
  
  import qualified Ra.Refs as Refs
  import Ra.GHC (GRHS_exprs, GRHS_binds)
  
  -- Note about making SymTables from bindings: `Fun` needs to be lifted to `HsExpr` through the `HsLam` constructor. This is to unify the type of the binding to `HsExpr` while retaining MatchGroup which is necessary at HsApp on a named function.
  type Sym = (Maybe SymTable, HsExpr Id)
  type SymTable = Map Id [Sym] -- the list is of a symbol table for partial function apps, and the expression.
  type StackTable = Tree (Id, SymTable) -- One entry for every level deep and every invokation in a stack frame, so separate invokations of the same function can be distinguished
  type StackBranch = [StackTable] -- nodes: consecutive ones are child-parent
  -- consider making alternative so the merge operation is more idiomatically `<|>`
  
  update_head :: (a -> a) -> [a] -> [a]
  update_head f (x:xs) = (f x):xs
  
  -- how to handle pattern bindings? the same way that we handle pattern matches.
  
  bind_to_table :: SymBranch -> HsBind Id -> SymBranch -- bind to newest stack frame
  bind_to_table (AbsBinds { abs_binds }) = unionsWith (++) (map (bind_to_table . unLoc) abs_binds)
  bind_to_table (FunBind { fun_id, fun_matches }) = singleton fun_id (HsLam fun_matches)
  bind_to_table (PatBind {  }) = 
  
  -- type NFStackTable = Map Id NF
  -- data NF = WHNF (HsExpr Id) | Ref (HsExpr Id)
  -- WHNF is either a literal, data construction, or unknown function app;
  -- Ref holds the expression that spits out the pipe that holds the value[s] that we must trace in a separate traversal over ref types. Note the Located because we use SrcSpan to find specific write instances
  
  deapp :: HsExpr Id -> (HsExpr Id, [HsExpr Id])
  deapp expr = case expr of
    HsApp l r -> (id *** (++[unLoc r])) (deapp $ unLoc l)
    _ -> (expr, [])
  
  pat_multi_match ::
    (HsExpr Id -> Maybe [HsExpr Id]) -- predicate and expression expander
    -> StackBranch -- full symbol table
    -> HsExpr Id
    -> [Pat Id]
    -> SymTable
  pat_multi_match expand stack table expr pats =
    let (table', values) = reduce_deep stack table expr
    in unionsWith (++) $ (values & map (\v ->
      case expand v of
        Just args | let arg_matches = map (uncurry pat_match stack) (zip args pats)
                  , none $ map null arg_matches -> unions arg_matches
        Nothing -> empty
    ))
  
  -- invoke as: `unions . concatMap (map ((unions . concatMap . pat_match table) . unLoc) . zip args . m_pats) mg_alts` on `MatchGroup`'s `mg_alts`
  pat_match ::
    StackBranch
    -> HsExpr Id
    -> Pat Id
    -> SymTable
  -- all new matches from the pat match; empty denotes the match failed (we'll bind wildcards under `_` which will be ignored later since it's an illegal variable and function name)
  -- Valid HsExpr: HsApp, OpApp, NegApp, ExplicitTuple, ExplicitList, (SectionL, SectionR) (for data types that are named by operators, e.g. `:`; I might not support this in v1 because it's so thin)
  -- Valid Pat: 
  -- empty pats
  pat_match branch expr = \case
    -- empty
    WildPat _ -> singleton (mkSystemName (mkVarOccUnique "_") (mkVarOcc "_")) ([], [expr])
    -- wrapper
    LazyPat pat -> pat_match table expr pat
    ParPat pat -> pat_match table expr pat
    BangPat pat -> pat_match table expr pat
    SigPatOut pat _ -> pat_match table expr pat
    -- base
    VarPat v -> singleton v ([], [expr])
    -- container
    ListPat pats -> unions $ map (pat_match expr) pats -- encodes the logic that all elements of a list might be part of the pattern regardless of order
    AsPat (L _ bind) pat -> union (singleton bind ([], [expr])) (pat_match table expr pat)
    TuplePat pats -> pat_multi_match (\case { ExplicitTuple args -> Just args; _ -> Nothing }) table expr pats
        
    ConPatOut{ pat_con = RealDataCon pat_con', pat_args = d_pat_args } -> case d_pat_args of
      PrefixCon pats -> pat_multi_match (\x ->
        let (con, args) = deapp x
        in if con == pat_con' then Just args else Nothing) table expr pats
      
      -- case expr of
      --   HsVar id | varName id == dataConName pat_con -> 
      --   HsApp l r -> 
      --     let fst $ iterate (\(l, args) -> case l of
      --       HsApp l' r' -> (l', (r' : args))
      --       HsCase mg ->  -- need to update the symbol table after pattern matching! Normally, it would be great to have that function that spits back the new symbol table and the tree of expressions. Then it should be a separate function that calls patterns matching. I forget why now I wanted to have it all done within pattern match. We already had the idea for this function. It drills all the way through args.
      --       _ -> )
      --   HsCase -> 
      --   let tied = tie expr
      --   in unions $ map (deapp . bool () (tie (table))) (snd tied)
      RecCon _ -> error "Record syntax yet to be implemented"
  
  reduce_deep :: StackBranch -> HsExpr Id -> [[HsExpr Id]] -> (StackBranch, [Sym]) -- is this Expr <-> Sym asymmetry okay in the arg/return okay?
  reduce_deep branch (HsLam mg) nf_args =
    let pat_matches :: SymTable
        pat_matches =
          (unLoc $ mg_alts mg) & map ( -- over function body alternatives
            uncurry (map ( -- over arguments
              merge_sym_tables . map ( -- over possible expressions
                uncurry pat_match
              ) . (uncurry zip) . (id *** repeat)
            )) . zip nf_args . map unLoc . m_pats . unLoc -- `nf_args` FINALLY USED HERE
          )
        next_arg_binds = unionsWith (++) (pat_matches : (maybeToList m_partial_binds))
    in if matchGroupArity mg < num_args
      then (branch'', [(Just next_arg_binds, HsLam (mg_drop num_args expr))]) -- partial
      else
        let next_explicit_binds :: SymTable
            next_explicit_binds = everythingBut (unionWith (++)) (
                (empty, False)
                `mkQ` ((,False) . bind_to_table)
                `extQ` (empty,) . ((\case 
                  HsApp _ _ -> True
                  HsLam _ -> True
                  _ -> False 
                ) :: HsExpr Id -> Bool) -- guard against applications and lambdas, which introduce bindings we need to dig into a scope to bind
              ) mg
            next_frame = Node (unionWith (++) next_explicit_binds next_arg_binds) []
            next_branch = next_frame : update_head (\cur_frame -> cur_frame{ subForest = next_frame : subForest cur_frame }) branch'
            next_exprs = concatMap (map (\GHRS _ body -> body)) (shallowest cast mg)
            next_args = map (drop (num_args - matchGroupArity mg)) nf_args
        in (merge_branches *** concat) . unzip . map (flip (reduce_deep next_branch) next_args) next_exprs
  
  reduce_deep branch (HsVar v) nf_args | not $ v `elem` map (fst . rootLabel) branch
                                         Just left_exprs <- (rootLabel frame) !? v =
    let num_args = length args
        flatten :: [(StackBranch, [a])] -> (StackBranch, [a])
        flatten = foldr (merge_branches *** (++)) ([], [])
        (left_branch, nf_left) = flatten $ map ( -- over all expressions
            flatten . map ( -- over all new expressions from reduce1
              flatten . map (uncurry reduce_deep) . uncurry zip . (
                repeat . (flip update_head) branch . union
                *** id
              ) . reduce1 branch'
            ) . (id***)
          ) next_exprs
        -- next_table = adjust (++(fst res)) v table -- BOOKMARK: finish unifying the reducing step between this app line and reduce_deep, then rename reduce_deep because this does more (incorporates arguments)
    in foldl (\(branch', nf_exprs) expr -> reduce_deep branch' expr nf_args) (left_branch, []) nf_left
    else (branch, [expr])
  
  reduce_deep branch (HsConLikeOut _) (_:_) = error "Only bare ConLike should make it to `reduce_deep`"
  reduce_deep branch expr@(HsConLikeOut) _ = (branch, [(Nothing expr)]) -- TERMINAL
  reduce_deep branch (HsLit _) (_:_) -> error "Application on Lit"
  reduce_deep branch (ExplicitTuple _) (_:_) -> error "Application on ExplicitTuple"
  reduce_deep branch ()
  
  -- 
  reduce1 :: StackBranch -> HsExpr Id -> (SymTable, [HsExpr Id]) -- only return new and updated entries, stop at names and literals... except I guess at a direct application? That dictates whether or not this is the thing that should update the stack table, or if it should just return a flat symbol table. 
  reduce1 table expr = case expr of
    -- ignore HsVar and HsApp, which should be fulfilled by the calling scope
    