module Ra where
  import Extra (***)
  import Data.Function.Syntax (*.)
  
  type SymTable = Map Id (Maybe (MatchGroup Id (HsExpr Id)), [HsExpr Id]) -- note the args are only necessary for explicit bindings; e.g. lambdas and named returns obviously aren't there
  
  deapp :: HsExpr Id -> Maybe (HsExpr, [HsExpr])
  deapp = \case
    HsApp l r -> fmap (id *** (++[r])) (deapp l)
    HsVar (L _ id) ->
      if varName id == dataConName pat_con
        then Just (v, [])
        else Nothing
  
  -- invoke as: `unions . concatMap (map ((unions . concatMap . pat_match table) . unLoc) . zip args . m_pats) mg_alts` on `MatchGroup`'s `mg_alts`
  pat_match :: SymTable -> HsExpr Id -> Pat Id -> SymTable
  -- Valid HsExpr: HsApp, OpApp, NegApp, ExplicitTuple, ExplicitList, (SectionL, SectionR) (for data types that are named by operators, e.g. `:`; I might not support this in v1 because it's so thin)
  -- Valid Pat: 
  -- empty pats
  pat_match table expr = \case
    -- empty
    WildPat _ -> Nothing
    -- wrapper
    LazyPat pat -> pat_match expr pat
    ParPat pat -> pat_match expr pat
    BangPat pat -> pat_match expr pat
    -- base
    VarPat id -> singleton id (Nothing, [expr])
    -- container
    ListPat pats -> unions $ map (pat_match expr) pats -- encodes the logic that all elements of a list might be part of the pattern regardless of order
    AsPat (L _ bind) pat -> liftA2 union (Just $ singleton bind (Nothing, [expr])) (pat_match expr pat)
    TuplePat pats -> 
      let tied = tie expr
      in snd tied & map $ \case
        ExplicitTuple args -> unions $ map (uncurry $ pat_match (fst tied)) $ zip args pats
        _ -> empty
        
    ConPatOut{ pat_con, pat_args } -> case pat_args of
      PrefixCon args -> case expr of
        HsVar id -> varName id == dataConName pat_con
        HsApp l r -> 
          let fst $ iterate (\(l, args) -> case l of
            HsApp l' r' -> (l', (r' : args))
            HsCase mg -> -- need to update the symbol table after pattern matching! Normally, it would be great to have that function that spits back the new symbol table and the tree of expressions. Then it should be a separate function that calls patterns matching. I forget why now I wanted to have it all done within pattern match. We already had the idea for this function. It drills all the way through args.
            _ -> )
        HsCase -> 
        let tied = tie expr
        in unions $ map (deapp . bool () (tie (table))) (snd tied)
      RecCon _ -> error "Record syntax yet to be implemented"
    let unravel :: ([HsExpr Id], HsExpr Id) -> ([HsExpr Id], HsExpr Id)
        unravel (args, (HsApp l r)) = ((unLoc r) : args, l)
        unravel = id
        app = fst $ iterate unravel ([unLoc r], l) in
    -- case pat of
        
  to_con :: SymTable -> HsExpr Id -> (SymTable, Forest (HsExpr Id)) -- the symbols after pattern matching, and we get a bunch of applications with constructors as the leaf of the tree (yes, this is an app tree). 
  to_con = to_con' [] where
    to_con' :: [[HsExpr Id]] -> SymTable -> HsExpr Id -> (SymTable, Forest Id) -- gonna experiment with returning Ids and just going all the way for these constructors and failing whenever we can't make it (e.g. imported functions)
    -- how can I resolve the arguments when it's not sufficiently applied at that point? In general we have a binding that has a certain type, which we could inspect to get whether or not it's a value type. Sure, I can screen this way but I still have to follow the value bindings; it's just a matter of adding an error condition, and that it's an optimization for speed. Then it should always be possible to see if we have enough arguments at the argument site by comparing against the size of the matchgroup patterns. If it's underargumented, then it's not matchable and we return empty list. Note that the argument list is the same length regardless of the path that you take because of type consistency
    to_con' args table expr = case expr of
      HsApp l r -> to_con' (r : args) table l -- (table, [Node r (to_con table l)])
      HsVar id | isUpper $ head $ occNameString $ nameOccName id -> (table )
               | Just (m_arg_pats, exprs') <- (table !? id) ->
                 case m_arg_pats of -- this is a function in general; do we need to pattern match? Yeah, that's why we update the symbol table. 
                   Just arg_pats | length m_pats $ unLoc arg_pats < length args ->
                    -- go from the list of accepted args, pattern matching against the 
                    let table' = foldl (unions *. (unions . map (pat_match table) . zip args . map unLoc . m_pats . unLoc)) empty (unLoc $ mg_alts args) -- seeing `zip [[HsExpr Id]] [LPat] -- need the new symbol table; basically a big ol' reduction with a cross product (impossible to tell when values co-occur)
                        cons = to_con' 
                    in (table', )
                   Nothing -> (table, [])
                 in foldl ((union *** (++)) *. to_con table') (empty, []) exprs' -- merge all the constructors that this variable could represent, and all the bindings that go behind that
               | otherwise -> undefined
      
      -- irreduceables
      
      _ -> []
  
  -- `tie` takes every expression to the expressions that aren't trivially reduceable: literals, function apps. Variables can be dereferenced from the bindings in the SymTable. Function calls could be data, and could need to be dereferenced. The problem is that HsApp is itself a representation, so the pattern matching has to be done at the same time as the dereferencing, which is actually fine. Then it just ties the HsApp, advancing by unravelling the left side until we get a constructor, then taking the intermediate representation local to the scope of pat_match. Then `tie` just hits an HsApp and returns.
  -- `tie` takes the expression and assumes as many of the arguments are bound as necessary, and reduces it to the `cov` argument, and leaves it at that (i.e. doesn't reduce this cov thing; all the logic for this is done in the head of one step. **Assume that the argument isn't an `HsApp`** because these should be dealt with in pattern matching. Although, doesn't that mean that we can merge the two? Nah, I should indeed, just match against the table and pass it to the pattern matcher)
  cov_exprs :: SymTable -> [HsExpr Id] -> (SymTable, [HsExpr Id])
  cov_exprs table exprs = map (cov_exprs' table) exprs where
    cov_exprs' :: SymTable -> HsExpr Id -> (SymTable, [HsExpr Id])
    cov_exprs' table expr = case expr of
      
      -- irreduceable exprs
      _ -> (table, expr)
      -- HsApp _ _ -> (table, expr)
      -- HsOpApp _ _ _ _ -> (table, expr)
      -- HsLam _ -> (table, expr)
      -- HsLamCase _ -> (table, expr)
      -- HsLit _ -> (table, expr)
      -- HsOverLit _ -> (table, expr)
      -- HsExplicitTuple _ _ -> (table, expr)
      
      -- wrappers
      HsPar e -> cov_exprs' e
      
      -- more interesting expressions
    cov_exprs' table expr@(HsLit _) = expr
    cov_exprs' table expr@(HsOverLit _) = expr
    
    -- wrappers
    cov_exprs' 
    cov_exprs' table expr' | (expr, args) <- deapp expr' = case expr of
        HsVar _ -> (table, expr)
        HsApp _ _ -> let d = deapp expr (pat_match table l)