module Ra.Extra (
  update_head
) where
  update_head :: (a -> a) -> [a] -> [a]
  update_head f (x:xs) = (f x):xs
