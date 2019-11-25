module U where

import Control.Concurrent.MVar

foo = do
  v <- newEmptyMVar
  putMVar v (0, 1)
  (a, _) <- readMVar v
  return a