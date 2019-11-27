module T where
  import Control.Concurrent.MVar
  
  -- foo = (do { x <- newEmptyMVar; return x }) >>= (\x -> putMVar x 42 >> return x) >>= readMVar
  
  bot x = bot x
  bar = do
    let bar _ = newEmptyMVar
    v0 <- bar ()
    v1 <- bar ()
    putMVar v1 1
    r1 <- readMVar v1
    r0 <- readMVar v0
    putMVar v0 r1
    putMVar v1 r0
    readMVar v0
  
  -- newtype Roll a = Roll (Roll a -> a)
  -- unroll (Roll a) = a
  
  -- fix f = fixH (Roll fixH)
  --   where 
  --     {-# NOINLINE fixH #-}
  --     fixH x = f ((unroll x) x)
  
  -- qux = let
  --   a = let a = 42 in a
  --   in a
    
  -- quux = fix (\x -> x)