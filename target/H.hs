{-# LANGUAGE MagicHash #-}

module H where
import Control.Concurrent.MVar
import Control.Concurrent (forkIO)

type Consumer a b = a -> b

foo :: IO Int
foo = do
  let x = 42
      y = bar x
  v <- newEmptyMVar
  w <- newEmptyMVar
  _ <- putMVar w (v, 42)
  _ <- putMVar v y
  (p, _) <- readMVar w -- resolving from the wrong stack: may be from hold flagging (one breakpoint surprisingly not hit). OHHHHH. This is a fundamental flaw with the pattern matching scheme, which matches against only previous symbols, not symbols in the same group (thanks to `letrec`). Crap. BOOKMARK
  forkIO (putMVar v y)
  readMVar p

bar :: Consumer a a
bar x = x