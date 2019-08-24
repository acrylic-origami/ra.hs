module A where

data D a b = D a b
  
foo :: Int -> D Int Int
foo _ = bar 3 where
  bar x = case x of
    4 | (c, d) <- (\x -> x + 6, (+5))
      , let e = 42 -> if 8 > 7 then D (c 9) e else (\x -> D (d 10) x) e

baz = foo 2