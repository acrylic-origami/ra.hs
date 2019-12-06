{-# LANGUAGE Rank2Types #-}

module Rg (
  map,
  filter,
  
  from,
  interval,
  
  scan,
  flatmap,
  buffer,
  
  combineLatest,
  zip,
  
  share
) where

import C.Union
import Prelude hiding ( map, filter, zip )
import qualified Prelude as P ( map, filter, zip )
import Data.Maybe ( fromMaybe )
import Data.STRef ( STRef(..), newSTRef, readSTRef, writeSTRef, modifySTRef )

import Data.Functor.Contravariant ( Contravariant(..), contramap, (>$) )

import Data.Functor ( ($>), (<$) )
import Control.Concurrent ( threadDelay )
import Control.Monad.ST ( ST(..), stToIO )
import Control.Monad ( void, forever )
import Control.Arrow ( (***), (&&&), first, second )
import Data.Bool ( bool )

type C a = a -> IO Bool
type S a = C a -> IO () -- IO because it must be at least partly stateful: it has to return the IO from the calls to its `C`
type O a b = C b -> C a
type OState m a b = C b -> m (C a)
type Share a = (S a, C a)

map :: (a -> b) -> O a b -- note not quite fmap (actually gmap, or contramap)
map = flip (.)

-- consider cofunctor

filter :: (a -> Bool) -> O a a -- (a -> IO Bool) -> a -> IO Bool
filter f = ((uncurry $ bool (return True)).) . (&&&f)
-- first outer scope bound to (C a), then waits while the whole thing is applied to v, so (a, Bool) -> the rest of the args to (bool a) (a, Bool) -> 

scan :: (a -> b -> b) -> b -> OState IO a b
scan f init down = stToIO $ do
  init' <- newSTRef init
  return $ \v -> stToIO (modifySTRef init' (f v) >> readSTRef init') >>= down

flatmap :: (a -> S b) -> O a b
flatmap = (((True<$).).) . flip -- what the fuck -- flatmap g down = flip g down

from :: Traversable t => t a -> S a
from = (void.) . flip mapM

interval :: Int -> S ()
interval delay = void . forever . ((threadDelay delay)>>) . ($())
-- equivalently `interval delay down = void . forever . do { threadDelay delay; down () }` -- just interesting to look at the point-form

buffer :: C [a] -> IO (C a, C b)
buffer down = stToIO $ do
  buf <- newSTRef []
  return (
      (True<$) . stToIO . (modifySTRef buf) . (:),
      const $ down =<< ( stToIO $ do
          buf' <- readSTRef buf
          writeSTRef buf []
          return buf'
        )
    )

combineLatest :: C (a, b) -> IO (C a, C b)
combineLatest down = stToIO $ do
  vs <- newSTRef (Nothing, Nothing) -- could maybe use Alternative computation, or fromMaybe equivalent but unlifting
  -- if both are Just, then send both through `down`, don't overwrite. Otherwise, `void`. (Maybe) -> Maybe () -> Maybe ST -coerce-> ST
  -- How to flip the container? How to lift? Through some kind of lifting function, (,) <$> v <*> v
  let zipf t = fromMaybe (return True) $ down <$> ((,) <$> fst t <*> snd t)
      proc f v = True <$ ((stToIO $ readSTRef vs) >>= zipf . f (v<$))
  
  return ( proc first, proc second )

zip :: C (a, b) -> IO (C a, C b)
zip down = stToIO $ do
  vs <- newSTRef ([], [])
  let zipf (a, b) = -- requires atomicity; STM?
        if length a > 0 && length b > 0 -- pull off the other one
          then down (head a, head b) >> (stToIO $ writeSTRef vs (tail a, tail b))
          else stToIO $ writeSTRef vs (a, b)
      proc f v = True <$ ((stToIO $ readSTRef vs) >>= (zipf . f (v:)))
  
  return ( proc first, proc second )
  
share :: (IO Bool -> IO Bool -> IO Bool) -> [C a] -> C a
share f t a = foldl f (return True) $ P.map ($a) t