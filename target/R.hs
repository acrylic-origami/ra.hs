module R where

import Control.Concurrent.MVar
-- import Control.Concurrent.STM
import Data.STRef
import Data.IORef

mvar = do
  mv0 <- newEmptyMVar
  mv1 <- newEmptyMVar
  putMVar mv0 (\x -> putMVar mv1 x)
  f <- readMVar mv0
  f (\x -> x)
  g <- readMVar mv1
  return (g 42)