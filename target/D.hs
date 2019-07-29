module D where

-- foo | Just a <- Just 42 = a + 3
baz | (a, b) <- (\x -> x 2, \y -> y + 1) = a b
bar = baz