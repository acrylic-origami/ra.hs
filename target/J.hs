module J where
  import Control.Concurrent.MVar
  
  foo = do
    v <- newEmptyMVar
    putMVar v ((), 42)
    b <- readMVar v
    return b
