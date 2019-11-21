module K where

import Control.Concurrent.MVar

foo = do
  v <- newEmptyMVar
  _ <- putMVar v 42
  j <- readMVar v
  return j