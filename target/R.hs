module R where

import Control.Concurrent.MVar
-- import Control.Concurrent.STM
import Data.STRef
import Data.IORef

bot x = bot x

io = do
  io0 <- newIORef (\_ -> 0)
  writeIORef io0 (\_ -> 1)
  writeIORef io0 bot
  v <- readIORef io0
  return (v ())

-- mvar = do
--   mv0 <- newMVar 2
--   let v = \_ -> putMVar mv0 3
--   v ()
--   v <- readMVar mv0
--   return v