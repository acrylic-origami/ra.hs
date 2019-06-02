module A where
foo :: a -> a
foo = \x -> x

bar :: a -> a -> a
bar a b = case True of
  True -> a
  _ -> b