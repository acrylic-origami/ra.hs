module V where
-- import qualified Rg
-- import C.Union
import qualified W
import Control.Monad.ST
import Data.STRef
-- import qualified W

type C a = a -> IO Bool
type OState m a b = C b -> m (C a)
scan :: (a -> b -> b) -> b -> OState IO a b
scan f init down = stToIO $ do
  init' <- newSTRef init
  return $ \v -> stToIO (modifySTRef init' (f v) >> readSTRef init') >>= down

c :: C a
c x = pure True
v :: IO Int
v = pure 2
foo = scan const (0 :: Int) c <*> v
