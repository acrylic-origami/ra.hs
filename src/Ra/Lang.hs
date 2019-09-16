{-# LANGUAGE TupleSections, DerivingFunctor #-}
module Ra.Lang (
  Sym(..),
  SymTable(..),
  StackBranch,
  Stack(..),
  stack_var_lookup,
  union_sym_tables,
  ReduceSyms(..),
  PatMatchSyms(..),
  Pipe,
  is_zeroth_kind,
  to_expr,
  mutate_expr,
  runIO_sym
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

type Sym = LHsExpr Id
type SymTable = Map Id [Sym] -- the list is of a symbol table for partial function apps, and the expression.
union_sym_tables = unionsWith (++)
-- ah crap, lambdas. these only apply to IIFEs, but still a pain.

type ThreadKey = [SrcSpan]
type Writes = Map Pipe [(ThreadKey, Sym)]
type Pipe = SrcSpan -- LHsExpr Id
data ReduceSyms = ReduceSyms {
  rs_syms :: [Sym],
  rs_writes :: Writes
}

data PatMatchSyms = PatMatchSyms {
  pms_syms :: SymTable,
  pms_writes :: Writes
}

-- type StackTable = SetTree StackFrame -- One entry for every level deep and every invokation in a stack frame, so separate invokations of the same function can be distinguished
newtype StackBranch = SB [(SrcSpan, SymTable)] deriving Functor -- nodes: consecutive ones are child-parent
data Stack = Stack {
  st_branch :: StackBranch,
  st_threads :: [Int]
}

instance Semigroup StackBranch where
  (<>) =
    let combine (Just (a_src, a_table)) (Just b@(b_src, b_table)) = assert (a_src == b_src) (second (union_sym_tables . (:[a_table])) b) -- prefer first (accumulating) branch
        combine Nothing (Just b) = b
        combine (Just a) Nothing = a
    in ((map (uncurry combine)).) . zipAll

instance Monoid StackBranch where
  mempty = SB mempty
  mappend = (<>)

instance Semigroup Stack where
  (Stack b_l t_l) <> (Stack b_r t_r) = Stack (b_l <> b_r) (t_l <> t_r)

instance Monoid Stack where
  mempty = Stack mempty mempty
  mappend = (<>)

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
  
is_zeroth_kind :: Sym -> Bool
is_zeroth_kind sym = case unLoc sym of
  HsLit _ -> True
  HsOverLit _ -> True
  ExplicitTuple _ _ -> True
  ExplicitList _ _ _ -> True
  _ -> False

to_expr :: Sym -> HsExpr Id
to_expr = unLoc

mutate_expr :: (HsExpr Id -> HsExpr Id) -> Sym -> Sym
mutate_expr = fmap -- this just happens to be the Functor definition of GenLocated

make_thread_key :: Stack -> ThreadKey
make_thread_key stack =
  if not $ null $ st_thread stack
    then drop ((length $ st_branch stack) - (head $ st_thread stack)) $ map fst $ st_branch stack
    else mempty

stack_var_lookup :: Id -> Stack -> Maybe [Sym]
stack_var_lookup v = branch_var_lookup v . st_branch

branch_var_lookup :: Id -> StackBranch -> Maybe [Sym]
branch_var_lookup v = foldr ((\t -> (<|>(t !? v))) . snd . coerce) Nothing  -- for some reason, `coerce` doesn't want to work here from some ambiguity that I can't understand

is_visited :: SrcLoc -> Stack -> Bool
is_visited = (flip elem) . map fst . st_branch

clear_branch :: StackBranch -> StackBranch
clear_branch = fmap $ map (second (const empty)) . coerce

update_head_table :: SymTable -> StackBranch -> StackBranch
update_head_table next_table = fmap $ update_head (second ((<>) . (:[next_table])))

union_branches :: [StackBranch] -> StackBranch
union_branches = mconcat

runIO_name :: Name
runIO_name = mkSystemName (mkVarOccUnique $ mkFastString "runIO#") (mkVarOcc "runIO#")
runIO_sym :: Sym
runIO_sym = mkLocalVar VanillaId runIO_name ty vanillaIdInfo
-- union_sym_tables :: [SymTable] -> SymTable
-- union_sym_tables = unionsWith (++) . map coerce -- TODO check if we need to be more sophisticated than this crude merge