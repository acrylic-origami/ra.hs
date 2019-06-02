module B where
  type Consumer a m = (a -> m Bool) -- oddly enough specifying `Monad m =>` doesn't help me omit labels later. Still have to understand why; instead using a GADT apparently does what we want
  type Operator a b ma mb mo = (Consumer a ma) -> mo (Consumer b mb)

  scan :: (b -> a -> b) -> b -> Operator a b ma mb IO
  scan f z0 c = do
    z' <- newMVar z0
    let {
      co_mod zp = do
        zn <- (flip f) zp;
        cont <- c zn
        return (cont, zn)
      co x = do
        -- I'm sure there's a more elegant and atomic way to do this
        z <- readMVar z'
        cz <- co_mod z
        putMVar $ snd cz
        return $ fst cz
    }
    return co