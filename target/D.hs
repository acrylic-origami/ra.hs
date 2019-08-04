module D where

-- foo | Just a <- Just 42 = a + 3
baz = baq where
  baq | let a = 42 = baw (a + 1)
  baw x = x
bar = baz
quux = Just 1