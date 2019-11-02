module J where
  import Control.Concurrent.MVar
  type Consumer x = x -> x
  
  foo = do
    x <- newEmptyMVar
    _ <- putMVar x (bar 42)
    readMVar x
  
  bar :: Consumer a
  bar x = x