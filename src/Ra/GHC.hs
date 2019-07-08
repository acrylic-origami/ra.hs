module Ra.GHC (
  GRHS_exprs,
  GRHS_binds
) where
  GRHS_exprs :: GenericQ [HsExpr Id]
  GRHS_exprs = map (\GRHS _ body -> body) . concat . shallowest cast
  GRHS_binds :: GenericQ SymTable
  GRHS_binds = everythingBut (unionWith (++)) (
      (empty, False)
      `mkQ` ((,False) . bind_to_table)
      `extQ` (empty,) . ((\case 
        HsApp _ _ -> True
        HsLam _ -> True
        _ -> False 
      ) :: HsExpr Id -> Bool) -- guard against applications and lambdas, which introduce bindings we need to dig into a scope to bind
    )