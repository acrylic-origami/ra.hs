{-# LANGUAGE OverloadedStrings, StandaloneDeriving, DeriveGeneric #-}
import Happstack.Server ( Response(..), ServerPart(..), Method(..), ToMessage(..), decodeBody, defaultBodyPolicy, dir, look, nullConf, simpleHTTP, method, toResponse, toResponseBS, ok, badRequest, serveDirectory, Browsing(..) )
import Happstack.Server.Types ( RqBody(..), Request(..) )
import Happstack.Server.Monads ( ServerMonad(..) )
import qualified Happstack.Server as HS

import Control.Arrow ( first, second, (&&&) )
import Control.Monad ( msum, join )

import Control.Concurrent.MVar ( takeMVar )
import GHC
import GHC.Generics ( Generic(..) )
import DynFlags
import GHC.Paths ( libdir )

import Data.Maybe ( fromMaybe )
import Data.Tree ( Tree(..) )
import Data.ByteString.Lazy.UTF8 as LUB ( fromString )
import Data.ByteString.Lazy as LB ( fromStrict, hPut )

import System.FilePath ( (</>) )

import Ra
import Ra.Impure
import Ra.Lang.Extra ( Tree2(..), ppr_sa, tree_sa, ppr_rs )
import Ra.Lang
import Ra.GHC.Translate
import Ra.GHC.Util ( varString )
import Outputable ( Outputable, interppSP, showSDocUnsafe, showPpr )

import System.Timeout ( timeout )
import System.IO ( openTempFile, hPutStr, hClose )
import System.Directory ( removeFile )
import Control.Exception ( try, bracket, SomeException(..) )
import Control.Monad.IO.Class ( liftIO )

import qualified Data.Aeson as Aeson

tc_bind :: TypecheckedModule -> [Bind]
tc_bind pgm =
  let tl_binds = grhs_binds False $ typecheckedSource pgm
      tl_frame = BindFrame $ SymTable {
              stbl_table = fromMaybe mempty $ or_pat_match_many tl_binds',
              stbl_binds = tl_binds'
            }
      tl_binds' = map (second (map (\sa -> sa { sa_stack = tl_frame : (sa_stack sa) }))) tl_binds
  in tl_binds'
  
max_time = floor 1E7

analyze :: [Bind] -> ReduceSyms
analyze = mconcat . map (reduce . snd)

tc_analyze :: GhcMonad m => TypecheckedModule -> m (Maybe ReduceSyms)
tc_analyze pgm = liftIO $ timeout max_time (return $! analyze $ tc_bind pgm)
  
both :: (a -> b) -> (a, a) -> (b, b)
both f (a, b) = (f a, f b)

deriving instance Generic (Tree2 a)
instance Aeson.ToJSON a => Aeson.ToJSON (Tree2 a) where
  toEncoding = Aeson.genericToEncoding Aeson.defaultOptions

alt_list [] b = b
alt_list a _ = a

explode :: [[a]] -> [[a]]
explode [] = [[]]
explode (h:t) = [ f a | f <- map (:) h, a <- explode t ]

un_tree2 :: Tree2 a -> [Tree a]
un_tree2 (Tree2 (a, x)) = map (Node a) (explode (map (concatMap un_tree2) x)) `alt_list` [Node a []]

reduce_ep :: ServerPart Response
reduce_ep = do
  method POST
  -- decodeBody "/tmp" 0 10000 10000
  rq <- askRq
  m_rs <- liftIO $ try $ bracket (do
        (fn, h) <- openTempFile "tmp" "tmp.hs"
        hPutStr h "module Test where\n"
        hPut h . unBody =<< (takeMVar $ rqBody rq)
        hClose h
        pure fn
      )
    (removeFile)
    (\fn -> runGhc (Just libdir) $ do
        dflags <- getSessionDynFlags
        
        setSessionDynFlags dflags
        
        target <- guessTarget fn Nothing
        setTargets [target]
        
        let mod = mkModuleName "Test"
        load (LoadUpTo mod)
        rs <- tc_analyze =<< typecheckModule =<< parseModule =<< getModSummary mod
        pure $ LUB.fromString . ppr_rs (showPpr dflags) <$> rs
        pure $ (Aeson.encode . both (map (un_tree2 . fmap (first (map (showPpr dflags))) . tree_sa (showPpr dflags))) . (rs_syms &&& rs_stmts)) <$> rs
      )
    
  case m_rs of
    Left e -> badRequest $ toResponseBS "text/plain" $ LUB.fromString $ "Exception while running: " ++ (show (e :: SomeException))
    Right m_rs' -> case m_rs' of
      Nothing -> badRequest $ toResponseBS "text/plain" "Analysis timed out, input may be too complex."
      Just rs -> ok $ toResponseBS "text/plain" rs

main :: IO ()
main = do
  putStrLn "Listening..."
  simpleHTTP nullConf { port=8002 } $ msum [
      dir "f" reduce_ep
      , dir "static" $ serveDirectory EnableBrowsing [] "./static"
      , serveDirectory DisableBrowsing ["index.html"] "./web/public"
    ]