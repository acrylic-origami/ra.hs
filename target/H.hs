{-# LANGUAGE MagicHash #-}

module H where
import Control.Concurrent.MVar
debug# :: a
debug# = undefined

type Consumer a b = a -> b

foo :: IO Int
foo = do
  let x = 42
      y = bar x
  v <- newEmptyMVar
  _ <- putMVar v y
  readMVar v

bar :: Consumer a a
bar x = x