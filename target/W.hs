module W where
import GHC.Base ( bindIO, returnIO, thenIO )
import qualified GHC.Base as G
-- import Control.Monad ( ap, liftM2 )

-- (<*>) :: Monad m => m (a -> b) -> m a -> m b
-- (<*>) = ap
-- liftA2 :: (a -> b -> c) -> IO a -> IO b -> IO c
-- liftA2 = liftM2

-- flip                    :: (a -> b -> c) -> b -> a -> c
-- flip f x y              =  f y x

const :: a -> b -> a
const x _ = x

($) :: (a -> b) -> a -> b
f $ g = f g

(.) :: (a -> b) -> (c -> a) -> c -> b
a . b = \x -> a (b x)

id x = x

ap                :: (Monad m) => m (a -> b) -> m a -> m b
ap m1 m2          = do { x1 <- m1; x2 <- m2; Prelude.return (x1 x2) }

(<*>) :: IO (a -> b) -> IO a -> IO b
(<*>) = G.ap

(>>=) :: IO a -> (a -> IO b) -> IO b
(>>=) = bindIO

(>>) :: IO a -> IO b -> IO b
(>>) = (Prelude.*>)

(*>) :: IO a -> IO b -> IO b
(*>) = thenIO

return :: a -> IO a
return = Prelude.pure

pure :: a -> IO a
pure  = returnIO
-- (>>=)     = bindIO