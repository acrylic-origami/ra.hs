module Q where
  import Control.Concurrent.MVar
  -- foo =
  --   let f _ = g ()
  --       g _ = f () -- CRAP.
  --   in g ()
  foo = do
    p <- newEmptyMVar
    let f = (\_ -> do
            g <- readMVar p
            g ()
          )
    putMVar p f
    f ()