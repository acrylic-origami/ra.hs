module E where
  class A a where
    foo :: a -> Int
    bar :: a -> Int
    
    foo x = bar x + 1
    bar x = foo x + 1
  
  instance A () where
    foo = const 42