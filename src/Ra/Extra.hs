module Ra.Extra (
  update_head
) where
  update_head :: (a -> a) -> [a] -> [a]
  update_head f (x:xs) = (f x):xs
  
  zipAll :: [a] -> [b] -> [(Maybe a, Maybe b)]
  zipAll (a:as) (b:bs) = (Just a, Just b) : zipAll as bs
  zipAll (a:as) [] = (Just a, Nothing) : zipAll as []
  zipAll [] (b:bs) = (Nothing, Just b) : zipAll [] bs
