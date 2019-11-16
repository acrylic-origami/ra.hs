module Q where
  import Control.Concurrent.MVar
  foo =
    let f _ = 42
        g _ = f () -- CRAP.
    in g ()
  -- foo = do
  --   p <- newEmptyMVar
  --   let f = (\_ -> do
  --           g <- readMVar p
  --           g ()
  --         )
  --   putMVar p (\_ -> return 42)
  --   f ()