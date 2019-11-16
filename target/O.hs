module O where
-- foo x = baz foo x
bar = (\x -> baz `quux` x) `quux` 42
baz x = x
quux f x = f x
-- qux f = let x = f x in x