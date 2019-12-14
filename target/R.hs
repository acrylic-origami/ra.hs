module R where

import Control.Concurrent.MVar
-- import Control.Concurrent.STM
import Data.STRef
import Data.IORef

f = do
  a <- newEmptyMVar
  b <- newEmptyMVar
  c <- newEmptyMVar
  d <- newEmptyMVar
  
  putMVar a ()
  
  -- fan-out
  av <- readMVar a
  putMVar b av
  putMVar c (av, ())
  
  -- fan-in
  bv <- readMVar b
  cv <- readMVar c
  putMVar d (bv, cv)
  
  readMVar d -- expect ((), ((), ()))