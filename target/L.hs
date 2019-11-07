module L where
  class Eq a => A a where
    bar :: (Eq b, A c) => a -> b -> c -> c
    
  instance A () where
    bar _ _ x = x
  
  foo :: ()
  foo = bar () () ()
  
  -- class Foo a where
  --   foo :: a -> a
  
  -- data Bar = Bar
  -- instance Foo Bar where
  --   foo x = x
  
  -- baz = foo Bar