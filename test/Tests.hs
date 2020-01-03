module Main (main) where

import Test.Framework ( defaultMain, testGroup )
import Test.Framework.Providers.HUnit

import Test.HUnit

import GHC
import DynFlags
import GHC.Paths ( libdir )
import Data.Maybe ( fromMaybe )
import Data.Generics ( extT, extQ, mkT, mkQ, everything, everywhere, gmapQ, gmapT, Data(..), GenericQ, GenericT )
import System.Timeout ( timeout )
import Control.Monad.IO.Class ( liftIO )
import Control.Arrow ( (&&&), (***), first, second )

import Debug.Trace ( trace )

import Ra
import Ra.Impure
import Ra.Lang.Extra
import Ra.Lang
import Ra.GHC.Translate

import Test.Util.Lang
import Test.Util.Typecheck
import Test.Util.Predicate

import Ra.GHC.Util ( varString )
import Ra.Lang.Extra
import Data.Generics.Extra
import Outputable ( Outputable, interppSP, showSDocUnsafe, showPpr )
import Var ( Var, varUnique, varType )

main = defaultMain [ pure_tests, pipe_tests ]

pure_tests = testGroup "Pure tests" [
    testCase "Top-level function recursion" $
      let pgm = unlines [
              "f x = f x",
              "g = f ()",
              "h = f f"
            ]
      in runGhc (Just libdir) $ tc_hang_test pgm
      
    , testCase "Top-level value recursion" $
      let pgm = unlines [
              "f = f"
            ]
      in runGhc (Just libdir) $ tc_hang_test pgm
      
    , testCase "`fix`-like recursion" $
      let pgm = unlines [
              "f g = let x = g x in x",
              "h = f (\\x -> x)"
            ]
      in runGhc (Just libdir) $ tc_hang_test pgm
      
    , testCase "Value recursion in let" $
      let pgm = unlines [
              "f =",
              "  let g = h",
              "      h = g",
              "  in (g, h)"
            ]
      in runGhc (Just libdir) $ tc_hang_test pgm
      
    , testCase "Pat-match-driven recursion" $
      let pgm = unlines [
              "f =",
              "  let (g, h) = (h, g)",
              "  in (g, h)"
            ]
      in runGhc (Just libdir) $ tc_hang_test pgm
  ]

pipe_tests = testGroup "Pipe tests" [
    testCase "Simple pipe" $
      let pgm = unlines [
              "import Control.Concurrent.MVar",
              "f = do",
              "  v <- newEmptyMVar",
              "  putMVar v ()",
              "  readMVar v"
            ]
          expect = tSA "()" []
      in runGhc (Just libdir) $ tc_test pgm (any_result_match or [expect])
    
    , testCase "Closure value dependencies" $
      let pgm = unlines [
              "import Control.Concurrent.MVar",
              "import GHC.Base ( returnIO )",
              "f = do",
              "  a <- newEmptyMVar",
              "  putMVar a ()",
              "  (\\_ -> do { v <- readMVar a; putMVar a v; returnIO v }) ()"
            ]
          expect = tSA "()" []
      in runGhc (Just libdir) $ tc_test pgm (any_result_match or [expect])
    
    , testCase "Recursive flows of non-recursive pipe values" $
      let pgm = unlines [
              "import Control.Concurrent.MVar",
              "import GHC.Base ( bindIO )",
              "f = do",
              "  a <- newEmptyMVar",
              "  readMVar a `bindIO` putMVar a"
            ]
      in runGhc (Just libdir) $ tc_hang_test pgm
      
    , testCase "Recursive flows of recursive pipe values" $
      let pgm = unlines [
              "import Control.Concurrent.MVar",
              "import GHC.Base ( bindIO )",
              "f = do",
              "  a <- newEmptyMVar",
              "  readMVar a `bindIO` (\\x -> putMVar a (():x))"
            ]
      in runGhc (Just libdir) $ tc_hang_test pgm
    
    , testCase "Fan-in and fan-out" $
      let pgm = unlines [
              "import Control.Concurrent.MVar",
              "f = do",
              "  a <- newEmptyMVar",
              "  b <- newEmptyMVar",
              "  c <- newEmptyMVar",
              "  d <- newEmptyMVar",
              "  ",
              "  putMVar a ()",
              "  ",
              "  -- fan-out",
              "  av <- readMVar a",
              "  putMVar b av",
              "  putMVar c (av, ())",
              "  ",
              "  -- fan-in",
              "  bv <- readMVar b",
              "  cv <- readMVar c",
              "  putMVar d (bv, cv)",
              "  ",
              "  readMVar d -- expect ((), ((), ()))"
            ]
          expect = tSA "()" [
              [tSA "()" []],
              [tSA "()" [
                [tSA "()" []],
                [tSA "()" []]
              ]]
            ]
      in runGhc (Just libdir) $ tc_test pgm (any_result_match or [expect])
    , testCase "Higher-level pipe left-hand dependencies" $
    let pgm = unlines [
            "import Control.Concurrent.MVar",
            "f = do",
            "  p <- newEmptyMVar",
            "  q <- newEmptyMVar",
            "  putMVar p (\\x -> putMVar q x)",
            "  f <- readMVar p",
            "  f (\\x -> ((), x))",
            "  g <- readMVar q",
            "  return (g ()) -- expect ((), ())"
          ]
        expect = tSA "return" [
            [tSA "()" [
              [tSA "()" []],
              [tSA "()" []]
            ]]
          ]
    in runGhc (Just libdir) $ tc_test pgm (any_result_match or [expect])
    
    -- , testCase "Nested pipes" $
    --   let pgm = unlines [
    --           "import Control.Concurrent.MVar",
    --           "f = do",
    --           "  p <- newEmptyMVar",
    --           "  q <- newEmptyMVar",
    --           "  r <- newMVar p",
    --           "  putMVar r q",
    --           "  ",
    --           "  putMVar q 0",
    --           "  putMVar p 1",
    --           "  ",
    --           "  s <- readMVar r",
    --           "  readMVar s"
    --         ]
    --       expect = tSA "0" []
    --   in runGhc (Just libdir) $ tc_test pgm (any_result_match [expect])
      
    , testCase "Default-value pipes" $
      let pgm = unlines [
              "import Data.IORef",
              "f = do",
              "  v <- newIORef 0",
              "  writeIORef v 1",
              "  readIORef v"
            ]
          expect = [tSA "0" [], tSA "1" []]
      in runGhc (Just libdir) $ tc_test pgm (all_result_match (uncurry (&&) . ((>0) . length &&& and)) expect)
      
    , testCase "Repetition with pipe constructor aliases" $
      let pgm = unlines [
              "import Control.Concurrent.MVar",
              "f = newMVar",
              "g = do",
              "  v <- f 0",
              "  w <- f 1",
              "  v <- readMVar v",
              "  w <- readMVar w",
              "  return (v, w) -- expect only (0, 1)"
            ]
          expect = [tSA "return" [[ tSA "()" [ [tSA "0" []], [tSA "1" []] ]]]]
      in runGhc (Just libdir) $ tc_test pgm (any_result_match (uncurry (&&) . ((>0) . length &&& and)) expect)
      
    , testCase "Repetition with empty pipe constructor aliases" $
      let pgm = unlines [
              "import Control.Concurrent.MVar",
              "f = newEmptyMVar",
              "g = do",
              "  v <- f",
              "  w <- f",
              "  putMVar v 0",
              "  putMVar w 1",
              "  v' <- readMVar v",
              "  w' <- readMVar w",
              "  return (v', w') -- expect only (0, 1)"
            ]
          expect = [tSA "return" [[ tSA "()" [ [tSA "0" []], [tSA "1" []] ]]]]
      in runGhc (Just libdir) $ tc_test pgm (any_result_match (uncurry (&&) . ((>0) . length &&& and)) expect)
      
    , testCase "Lambda recursion through pipe" $
      let pgm = unlines [
              "import Control.Concurrent.MVar",
              "f = do",
              "  v <- newEmptyMVar",
              "  let g _ = do",
              "        g' <- readMVar v",
              "        g' ()",
              "  putMVar v g",
              "  g ()"
            ]
      in runGhc (Just libdir) $ tc_hang_test pgm
      
    , testCase "Value recursion through pipe" $
      let pgm = unlines [
              "import Control.Concurrent.MVar",
              "f = do",
              "  v <- newMVar f",
              "  f' <- readMVar v",
              "  f'"
            ]
      in runGhc (Just libdir) $ tc_hang_test pgm
        
    , testCase "Simple desugared `do` with pipes" $
      let pgm = unlines [
              "import Prelude hiding ( (>>), (>>=) )",
              "import Control.Concurrent.MVar",
              "import GHC.Base ( bindIO, thenIO )",
              "(>>=) = bindIO",
              "(>>) = thenIO",
              "f = newEmptyMVar",
              "  >>= (\\v -> putMVar v () >> readMVar v)"
            ]
          expect = [tSA "()" []]
      in runGhc (Just libdir) $ tc_test pgm $ any_result_match or expect
  ]