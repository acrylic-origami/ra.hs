module R where

import Control.Concurrent.MVar
-- import Control.Concurrent.STM
import Data.STRef
import Data.IORef

-- io = do
--   io0 <- newIORef (\_ -> 0)
--   writeIORef io0 (\_ -> 1)
--   writeIORef io0 bot
--   v <- readIORef io0
--   return (v ())


-- y f =
--   let x z = f (z z)
--   in f (x x)

fix :: (a -> a) -> a
fix f = let x = f x in x

-- foo = fix id

mvar = do
  mv0 <- newMVar fix
  v <- readMVar mv0
  return (v (\x -> x))