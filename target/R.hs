module R where

import Control.Concurrent.MVar
-- import Control.Concurrent.STM
import Data.STRef
import Data.IORef

f = newEmptyMVar
g = do
  v <- f
  w <- f
  putMVar v 0
  putMVar w 1
  v' <- readMVar v
  w' <- readMVar w
  return (v', w')