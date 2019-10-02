{-# LANGUAGE MagicHash #-}

module H where

debug# :: a
debug# = undefined

type Consumer a b = a -> b

foo :: IO Int
foo = do
  let x = 42
      y = bar x
  return y

bar :: Consumer a a
bar x = x