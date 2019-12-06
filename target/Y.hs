module Y where

foo :: Functor m => m a -> m Int
foo x = 1 <$ x

bar = foo Nothing