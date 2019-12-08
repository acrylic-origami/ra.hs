module V where
-- import qualified Rg
-- import qualified W
-- import qualified W

-- foo = Rg.scan const (0 :: Int) (const (return True)) <*> (return 2 :: IO Int)
-- foo :: IO Integer
-- foo = return id <*> return 0
-- bar :: IO Integer
-- bar = return 1 >>= return
-- import qualified InstMonadIO
-- import qualified C.GHC.Base
import C.Union


baz :: IO Integer
baz = return 2 >> return 42

-- foo :: 