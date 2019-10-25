module Ra.Extra (
  update_head,
  zipAll,
  list_alt,
  map_alt
) where
  import qualified Data.Map.Strict as M
  
  update_head :: (a -> a) -> [a] -> [a]
  update_head f (x:xs) = (f x):xs
  
  zipAll :: [a] -> [b] -> [(Maybe a, Maybe b)]
  zipAll (a:as) (b:bs) = (Just a, Just b) : zipAll as bs
  zipAll (a:as) [] = (Just a, Nothing) : zipAll as []
  zipAll [] (b:bs) = (Nothing, Just b) : zipAll [] bs
  zipAll [] [] = []
  
  lumpAll :: [[a]] -> [[a]] -> [[a]]
  lumpAll (x:xs) (y:ys) = (x ++ y) : lumpAll xs ys
  lumpAll [] (y:ys) = y : lumpAll [] ys
  lumpAll (x:xs) [] = x : lumpAll xs []
  
  list_alt :: [a] -> [a] -> [a]
  list_alt a@(_:_) _ = a
  list_alt _ b = b
  
  map_alt :: M.Map k v -> M.Map k v -> M.Map k v
  map_alt a b | M.null a = b
              | otherwise = a