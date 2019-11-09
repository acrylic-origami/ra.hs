module L where
  import qualified Prelude as P
  import qualified Prelude as PP
  -- class Eq a => A a where
  --   bar :: (Eq b, A c) => a -> b -> c -> c
    
  -- instance A () where
  --   bar _ _ x = x
  
  -- foo :: ()
  -- foo = bar () () ()
  
  baz :: P.Maybe a
  baz = P.Nothing
  
  quux :: PP.Maybe a
  quux = PP.Nothing
  
  -- class Foo a where
  --   foo :: a -> a
  
  -- data Bar = Bar
  -- instance Foo Bar where
  --   foo x = x
  
  -- baz = foo Bar