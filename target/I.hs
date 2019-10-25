module I where
  import Control.Concurrent.MVar
  
  data Z a b = Z a b
  
  foo =
    let x = \a b -> a + b
        z = if False then 42 else 56
        a | False = 12
          | True = a
        c = Z a a
        Z b _ = c
        y = b
    in do
      v <- newEmptyMVar
      putMVar v 42
      return y
  
  -- foo = do
  --   v <- newEmptyMVar
  --   putMVar v 42