module U where

import Control.Concurrent.MVar

foo = do
  let bar _ = newEmptyMVar
  v <- bar ()
  putMVar v (0, 1)
  (a, _) <- readMVar v
  return a