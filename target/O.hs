module O where
foo x = baz foo x
bar = baz baz (baz 42)
baz x = x
quux = foo 42
qux f = let x = f x in x