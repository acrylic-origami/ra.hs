module K where

import Control.Concurrent.MVar

foo = do
  j <- readMVar undefined
  return j