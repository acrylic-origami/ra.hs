module W where

import GHC.Types
import GHC.Classes
import GHC.CString
import GHC.Magic
import GHC.Prim
import Prelude (Semigroup(..))
-- import GHC.Prim.Ext
import GHC.Err
import GHC.Maybe
import GHC.IO (failIO,mplusIO)

import GHC.Tuple ()              -- Note [Depend on GHC.Tuple]
import GHC.Integer ()            -- Note [Depend on GHC.Integer]
import GHC.Natural ()            -- Note [Depend on GHC.Natural]

-- for 'class Semigroup'
import GHC.Real (Integral)
import {-# SOURCE #-} Data.Semigroup.Internal ( stimesDefault
                                              , stimesMaybe
                                              , stimesList
                                              , stimesIdempotentMonoid
                                              )

-- import Prelude hiding ( Applicative(..), Monad(..) )
import GHC.Base ( bindIO )
-- import Control.Monad ( ap, liftM2 )

-- (<*>) :: Monad m => m (a -> b) -> m a -> m b
-- (<*>) = ap
-- liftA2 :: (a -> b -> c) -> IO a -> IO b -> IO c
-- liftA2 = liftM2

-- flip                    :: (a -> b -> c) -> b -> a -> c
-- flip f x y              =  f y x

-- const :: a -> b -> a
-- const x _ = x

-- ($) :: (a -> b) -> a -> b
-- f $ g = f g

-- (.) :: (a -> b) -> (c -> a) -> c -> b
-- a . b = \x -> a (b x)

-- id x = x

-- (>>) :: IO a -> IO b -> IO b
-- (>>)      = (*>)
(>>=)     = bindIO