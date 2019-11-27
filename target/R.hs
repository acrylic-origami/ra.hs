module R where

import Control.Concurrent.MVar
-- import Control.Concurrent.STM
import Data.STRef
import Data.IORef

bot x = bot x

io = do
  io0 <- newIORef (\_ -> 0)
  writeIORef io0 (\_ -> 1)
  v <- readIORef io0
  return (v ())

mvar = do
  mv0 <- newEmptyMVar
  putMVar mv0 (\x -> x)
  v <- readMVar mv0
  return (v 1)


-- y f =
--   let x z = f (z z)
--   in f (x x)

-- fix :: (a -> a) -> a
-- fix f = let x = f x in x

-- foo = fix id