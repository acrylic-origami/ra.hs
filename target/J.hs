module J where
  import Control.Concurrent.MVar
  -- import C.Union
  type Consumer x = x -> x
  
  foo = do
    x <- newEmptyMVar
    _ <- putMVar x `baz` bar 42
    readMVar x
  
  bar :: Consumer a
  bar x | True = x
  
  baz f x = f x