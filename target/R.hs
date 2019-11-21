module R where

import Control.Concurrent.MVar
-- import Control.Concurrent.STM
import Data.STRef
import Data.IORef

bot x = bot x

mvar = do
  mv0 <- newMVar 2
  let v = \_ -> putMVar mv0 3
  v ()
  v <- readMVar mv0
  return v