Things I'm not supporting in v1:

- Pattern matches
	- Pattern matching is core to static analysis. It greatly enhances specificity by replacing the very weak law that anything entering a constructor might be incident on an argument to one much more nuanced, where certain parts and certain program locations can be part incident on certain locations. The results can then be hyper-specific, naming even the constructions that might be at a certain location, e.g. causing race conditions in rahse's case. **However:**
		1. Pattern matching + pipe resolution together create unknown instances after a single run of `reduce_deep`. This is because values coming out of pipes that need to be pattern-matched need to be paused until _all_ values are definitely extracted from the pipe, including ones that could be written _within expressions depending on the value being bound_. It's not as simple to avoid cycles here because processing these values are deferred for a given reduce iteration, and hence must hold onto all their stack information.
		2. `do` blocks that have bound values suffer, because statements below the binding rely on the binding for values, and hence require re-running after the final binding[s], although which ones are hard to pin down and requires another sweep of recursion over the AST.
	- This is an extremely high-priority feature that has an equally tall barrier to overcome. Note the plumbing for pattern matching is already in place for pure code and single iterations over stateful code. However, the entire structure of the program needs to be overhauled to support this feature in its most glorious generality.
- Record syntax patterns
	- Lots of complications:
		1. Record update is actually very annoying to represent, as the desugared version is an updater for every field
		2. Normal forms are more complicated: we either need a new `Sym` just for objects defined through record syntax or a mapping to the datatype declaration (cf. 3.)
		3. Record patterns are more complicated: at the very least, we need to use the existing auto-generated function to access the given record, and at worst, if that one is actually useless, we need to write our own. Hopefully too, this is compatible with our internal representation. If the representation is only the function call syntax (i.e. `HsApp Con ...`), then we need to cross-reference against the datatype declaration.
- Tuple sections
	- Need to wrap within a lambda that we construct ourselves in order to desugar (after typechecker, the syntax is still preserved, with `Missing` vs. `Present` tuple fields)
- Explicit type applications
	- _Something something_ phantom types _something something_. There might actually not be a problem with this: we just ignore it, unless the type being applied is `IO`.
- Recursive threading (e.g. `replicateM_ 10 (forkIO $ do ...)`) and its more subtle incarnations (e.g. `op $ replicateM 10 (share (merge printSub))`)
	- This functionality is **critical** for this tool to be usable, but it's also a substantial challenge. It's not easy to identify recursion, and the analysis of an unknown number of forks needs to be distinct from the analysis of exactly one for the given condition being analyzed. In particular, the fact that there could be 0 or >= 2 threads that pop up here is a very important condition. For ReactiveX race conditions the ">= 2" case will change results.
- Annotating decomposed/flowed values with rationale
	- This is an important piece of functionality for this tool, but also requires a lot of extra information to haul around. Before tackling this, it would be wise to consult typecheckers (e.g. Hack's) to see how they build error messages from multiple points of inference.
- Recursive applications of partial functions (e.g. `fix (fib_with 2)`)
	- Also in part because there is functionality to identify recursion statically at the moment. The code that checks the stack for cycles in `reduce_deep` is too sensitive at the moment. If a function sitting in the same spot is called more than once, the recursion will quit on that branch altogether. However, partial functions can be parameterized in different ways along the branch with non-trivial effect. 
- `unsafePerformIO` and any other IO unboxing (i.e. `IO a -> a`), to enforce that all IO refs be within IO blocks
	 - Confine the magic to IO, so we can confine the reference processing to just the `do` blocks and monadic operations (`>>`, `>>=`, etc.)
- Parallel monad comprehensions (see `HsDo` `ParStmt` case)
	- For lack of understanding their exact semantics. How does this interact with the `fork` code?
- Type families or `cast`, i.e. type-driven logic
	- Could vastly reduce our specificity: imagine a result from `everything` that just picks up... everything.