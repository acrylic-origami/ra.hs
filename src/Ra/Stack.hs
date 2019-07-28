{-# LANGUAGE TupleSections #-}
module Ra.Stack (
  SetTree(..),
  SetForest,
  Sym(..),
  SymTable(..),
  StackBranch,
  branch_lookup,
  union_branches,
  union_sym_tables,
  mksym,
  show_sym,
  show_table
) where
  
import GHC
import Outputable (showPpr)

import Data.Tuple.Extra ( second, (***) )
import Data.Coerce ( coerce )
import Data.Map.Strict ( Map(..), empty, union, unionsWith, toList, fromList, (!?) )
import qualified Data.Map.Strict as M ( map, mapWithKey )
import Data.Set ( Set(..) )
import Control.Applicative ( (<|>) )
import Control.Exception ( assert )

import Ra.Extra ( update_head, zipAll )

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
show_sym :: DynFlags -> Sym -> String
show_sym dflags = show . (((show_table dflags)<$>) *** showPpr dflags) . (\(Sym a) -> a)
show_table :: DynFlags -> SymTable -> String
show_table dflags = show . fromList . map (showPpr dflags *** map (show_sym dflags)) . toList . (\(SymTable t) -> t)

mksym :: HsExpr Id -> Sym
mksym = Sym . (Nothing,)

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
branch_lookup :: Id -> StackBranch -> Maybe [Sym]
branch_lookup v = foldr ((\(SymTable a) -> (<|>(a !? v))) . snd) Nothing  -- for some reason, `coerce` doesn't want to work here from some ambiguity that I can't understand
clear_branch :: StackBranch -> StackBranch
clear_branch = map (second (const $ SymTable empty))
update_head_table :: SymTable -> StackBranch -> StackBranch
update_head_table next_table = update_head (second (union_sym_tables . (:[next_table])))
-- consider making alternative so the merge operation is more idiomatically `<|>`

union_branches :: [StackBranch] -> StackBranch
union_branches = 
  let combine (Just (a_src, a_table)) (Just b@(b_src, b_table)) = assert (a_src == b_src) (second (union_sym_tables . (:[a_table])) b) -- prefer first (accumulating) branch
      combine Nothing (Just b) = b
      combine (Just a) Nothing = a
      folder :: StackBranch -> StackBranch -> StackBranch
      folder = ((map (uncurry combine)).) . zipAll
  in foldl1 folder

union_sym_tables :: [SymTable] -> SymTable
union_sym_tables = SymTable . unionsWith (++) . map coerce -- TODO check if we need to be more sophisticated than this crude merge