{-# LANGUAGE TupleSections #-}
module Ra.Stack (
  Sym(..),
  SymTable(..),
  StackBranch,
  branch_lookup,
  union_branches,
  union_sym_tables,
  ReduceSyms(..),
  PatMatchSyms(..)
) where


import GHC
import Outputable (showPpr)

import Data.Tuple.Extra ( second, (***) )
import Data.Coerce ( coerce )
import Data.Map.Strict ( Map(..), empty, union, unionWith, unionsWith, toList, fromList, (!?) )
import qualified Data.Map.Strict as M ( map, mapWithKey )
import Data.Set ( Set(..) )
import Data.Semigroup ( Semigroup(..), (<>) )
import Data.Monoid ( Monoid(..), mempty, mconcat )
import Control.Applicative ( (<|>) )
import Control.Exception ( assert )

import Ra.Extra ( update_head, zipAll )

-- Note about making SymTables from bindings: `Fun` needs to be lifted to `HsExpr` through the `HsLam` constructor. This is to unify the type of the binding to `HsExpr` while retaining MatchGroup which is necessary at HsApp on a named function.

-- class Symbol s where
--   mksym :: HsExpr Id -> s
--   unsym :: s -> HsExpr Id -- this seems really unidiomatic

-- instance Symbol Sym where
--   mksym = id
--   unsym = id

-- instance ReduceSyms 

type Sym = HsExpr Id
type SymTable = Map Id [Sym] -- the list is of a symbol table for partial function apps, and the expression.
union_sym_tables = unionsWith (++)
-- ah crap, lambdas. these only apply to IIFEs, but still a pain.

type Pipe = SrcSpan -- LHsExpr Id
data ReduceSyms = ReduceSyms {
  rs_syms :: [Sym],
  rs_writes :: Map Pipe [Sym]
}

data PatMatchSyms = PatMatchSyms {
  pms_syms :: SymTable,
  pms_writes :: Map Pipe [Sym]
}

instance Semigroup ReduceSyms where
  (ReduceSyms lsyms lwrites) <> (ReduceSyms rsyms rwrites) = ReduceSyms (lsyms <> rsyms) (unionWith (++) lwrites rwrites) -- is there a nicer way to do this?
  
  -- vs. (<>) = curry $ uncurry ReduceSyms . ((uncurry (++) . fmap rs_syms) &&& (uncurry (unionWith (++)) . fmap rs_syms))

instance Monoid ReduceSyms where
  mempty = ReduceSyms mempty mempty
  mappend = (<>)
  
instance Semigroup PatMatchSyms where
  (PatMatchSyms lsyms lwrites) <> (PatMatchSyms rsyms rwrites) = PatMatchSyms (union_sym_tables [lsyms, rsyms]) (unionWith (++) lwrites rwrites)

instance Monoid PatMatchSyms where
  mempty = PatMatchSyms mempty mempty
  mappend = (<>)

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
branch_lookup v = foldr ((\t -> (<|>(t !? v))) . snd) Nothing  -- for some reason, `coerce` doesn't want to work here from some ambiguity that I can't understand
clear_branch :: StackBranch -> StackBranch
clear_branch = map (second (const empty))
update_head_table :: SymTable -> StackBranch -> StackBranch
update_head_table next_table = update_head (second (union_sym_tables . (:[next_table])))
-- consider making Alternative so the merge operation is more idiomatically `<|>`

union_branches :: [StackBranch] -> StackBranch
union_branches = 
  let combine (Just (a_src, a_table)) (Just b@(b_src, b_table)) = assert (a_src == b_src) (second (union_sym_tables . (:[a_table])) b) -- prefer first (accumulating) branch
      combine Nothing (Just b) = b
      combine (Just a) Nothing = a
      folder :: StackBranch -> StackBranch -> StackBranch
      folder = ((map (uncurry combine)).) . zipAll
  in foldl1 folder

-- union_sym_tables :: [SymTable] -> SymTable
-- union_sym_tables = unionsWith (++) . map coerce -- TODO check if we need to be more sophisticated than this crude merge