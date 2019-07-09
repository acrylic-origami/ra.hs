{-# LANGUAGE TupleSections #-}
module Ra.Stack (
  SetTree(..),
  SetForest,
  Sym(..),
  SymTable(..),
  StackFrame(..),
  StackBranch,
  merge_branches,
  merge_sym_tables,
  mksym
) where
  import GHC
  
  import Data.Coerce (coerce)
  import Data.Map.Strict (Map, unionsWith)
  import Data.Set (Set)
  
  data SetTree v = Node {
    rootLabel :: v,
    subForest :: SetForest v
  }
  instance Eq a => Eq (SetTree a) where
    (Node{ rootLabel = left }) == (Node{ rootLabel = right }) = left == right
  instance (Ord a) => Ord (SetTree a) where
    (Node{ rootLabel = left }) <= (Node{ rootLabel = right }) = left <= right
  type SetForest v = Set (SetTree v)
  
  -- Note about making SymTables from bindings: `Fun` needs to be lifted to `HsExpr` through the `HsLam` constructor. This is to unify the type of the binding to `HsExpr` while retaining MatchGroup which is necessary at HsApp on a named function.
  newtype Sym = Sym (Maybe SymTable, HsExpr Id)
  newtype SymTable = SymTable (Map Id [Sym]) -- the list is of a symbol table for partial function apps, and the expression.
  -- ah crap, lambdas. these only apply to IIFEs, but still a pain. 
  
  mksym :: HsExpr Id -> Sym
  mksym = Sym . (Nothing,)
  
  type StackFrame = (Maybe Id, SymTable)
  
  -- data StackFrame = Frame {
  --   sf_id :: Maybe Id,
  --   sf_table :: SymTable
  -- }
  -- instance Eq StackFrame where
  --   (Frame{ sf_id = l }) == (Frame{ sf_id = r }) = l == r
  -- instance Ord StackFrame where
  --   (Frame{ sf_id = l }) <= (Frame{ sf_id = r }) = l <= r
    
  -- type StackTable = SetTree StackFrame -- One entry for every level deep and every invokation in a stack frame, so separate invokations of the same function can be distinguished
  type StackBranch = [(SrcSpan, SymTable)] -- nodes: consecutive ones are child-parent
  -- consider making alternative so the merge operation is more idiomatically `<|>`
  
  merge_branches :: [StackBranch] -> StackBranch
  merge_branches = undefined -- TODO the implementation around this needs to be changed, as I've realized that many updates will compete, with no bearing on which elements have been pushed closed to normal form
  
  merge_sym_tables :: [SymTable] -> SymTable
  merge_sym_tables = coerce . unionsWith (++) . map (coerce :: SymTable -> Map Id [Sym]) -- TODO check if we need to be more sophisticated than this crude merge