# ra.hs

ra.hs is <b>R</b>eactive <b>A</b>nalytics for Haskell. It is a non-recursive [symbolic execution engine](https://en.wikipedia.org/wiki/Symbolic_execution) that understands threads and thread-safe shared variables. It steps through the AST of a program to find possible non-recursive values at points in the program, including those that come from things like `IORef`. ra.hs then tracks forks to identify what threads are writing where.

Symbolic analysis can be thought of as sitting somewhere between typechecking and execution. It is able to reduce some regions of the typechecked AST by brute-forcing all possible branches and guards, provided that there exist values in the execution context/stack to fulfill pattern matches. On the other hand, the analysis is totally static, and in this engine, it is also non-recursive. By design, ra.hs should also always halt.

## Basic examples

Here are a few simple but illustrative examples:

- `f = const g h` reduces to `f = g`
- `f = do { v <- newEmptyMVar; putMVar v (); readMVar v }` reduces to `f = IO ()`&#42;.

For use on practical programs, the top-level function under test is saturated where necessary with `undefined`, then the program is executed symbolically. All writes to shared variables are logged and all possible non-recursive results for the function under test are returned.

&#42;<sup>ra.hs handles IO and STM monad laws implicitly and "transparently", so results are actually unwrapped, without IO or STM constructors around them. Thus in this example you would actually see `f = ()` directly.</sup>

For a slightly more involved example, consider this web server that responds to a request with a cache vs. database race:

```haskell
listenHTTP :: Int -> IO Socket
read :: Socket -> IO String
send :: Socket -> String -> IO ()
toRequest :: String -> Request
type Route u = (u, Req -> String)
dispatch :: URI u => Request -> [Route u]
db : Database
cache :: Cache

main = do
	sock <- listenHTTP 80
	forever $ do -- :: IO ()
		req <- toRequest <$> read sock
		send sock $ dispatch req $ [
			("/public/*", \req' -> do
					assets <- newEmptyMVar
					forkIO $ do 
						assets' <- getDBAssets db req'
						(fromMaybe assets' <$> tryReadMVar assets) >>= putMVar assets
					forkIO $ do
						assets' <- getCacheAssets cache req'
						(fromMaybe assets' <$> tryReadMVar assets) >>= putMVar assets
						
					(send . render) <$> readMVar assets
				)
			-- ...
		]
```

The forked threads initiate the race condition to `putMVar` on `assets :: MVar Assets`. Notably, this is done at two separate locations in the program. Race conditions of this sort are amenable to analysis by ra.hs, as opposed to, say a race from threads spawned by iterating a list (a recursive data type).

The race is contained within a lambda `\req' -> ...` which will only be explored by ra.hs when it is called by the body of `dispatch`, and provided ra.hs has access to its source. This will be discussed further in [limitations](#limitations).

## Use
	
ra.hs analyzes `base` functions with [`purebase`](https://github.com/acrylic-origami/purebase), a custom Prelude that can be typechecked by the GHC API and doesn't conflict with uses of Prelude in the target source. So that the GHC API resolves `purebase`, **you need to `import qualified C.Union` to the top-level module**. ra.hs employs type matching to find all top-level declarations, so while this is a no-op since the qualified import means `purebase` won't be compiled into your code, it will be available to ra.hs.

ra.hs itself includes a GHC frontend plugin so it can find the Cabal modules of the code under test (following a great suggestion of Edward Yang's [@ezyang.com](http://blog.ezyang.com/2017/02/how-to-integrate-ghc-api-programs-with-cabal/)). It's called through the `--with-ghc`/`-w` option of `cabal repl`, which points to its executable after building, somewhere in `dist` or `new-dist` depending on the version of cabal. A proper call looks something like this:

	cabal repl -w dist-newstyle/build/x86_64-osx/ghc-8.6.5/ra.hs-0.1.0.0/x/ra.hs/build/ra.hs/ra <module-under-test>

## Limits to analysis<a name="limitations">&nbsp;</a>

If the body for a function (e.g. `dispatch` above) is not accessible to ra.hs, then the block representing its application to arguments is symbolized and passed flows through the rest of the program as a normal form. This has two consequences:

1. Unsaturated lambda arguments are never executed.
2. All pattern matches other than top-level variable and wildcard patterns will fail.

It is worth emphasizing that ra.hs does not synthesize arguments and combinations of arguments to generate behaviors for functions it failed to resolve. This allows it to be perfectly selective for pattern matches at the expense of sensitivity. In the case of `dispatch` for example, the unsaturated lambda argument `\req' -> ...` is already a normal form, so the whole block `dispatch req (\req' -> ...)` will be substituted wherever it's referenced, in this case in the second argument of `send`.

This approach is not related to another behavior of ra.hs to examine all IO side effects that it can (obeying the above behavior) regardless of if they contribute to the final return value: this is what is meant by ra.hs "understanding" shared state.

## Trajectory

ra.hs was originally started to detect race conditions in Reactive programs, by evaluating the rule that different threads can't write values from the same source to the same shared variable.

For now, this analysis is a first-class citizen to the ra.hs ecosystem, although a non-intrusive, additive one as it does not impact any core functionality. It adds a state variable to track value sources (arguments to `Consumer` types) and an `HsVar` guard to identify when expressions are incident on `Consumer` types. This extra state is combined with the core thread and write tracking to identify violations to this rule. This may be temporary, depending on how flexible the ra.hs engine can be and what kinds of generalization can be applied.