module G where

class A a where
  foo :: a
  
instance A () where
  foo = ()
  
instance A Int where
  foo = 42