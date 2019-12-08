{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Z where
-- bug case:
class F a where
  foo :: a

newtype G a = G a deriving F

-- MVE:
f :: a
f = f