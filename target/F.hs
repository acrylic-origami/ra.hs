{-# LANGUAGE MonadComprehensions, TransformListComp, ParallelListComp #-}
module F where

import Data.List ( elemIndex )

foo :: [Int]
foo = [x+y | x <- [1,2,3]
           | y <- [4,5,6] ]
  -- baz <- Just 56
  -- let foo = succ (42 :: Int)
  -- bar <- foo `elemIndex` [44 :: Int]
  -- return $ pred bar + baz