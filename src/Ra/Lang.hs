{-# LANGUAGE TupleSections, DeriveFunctor #-}
module Ra.Lang (
  Sym(..),
  SymTable(..),
  StackBranch(..),
  unSB,
  mapSB,
  Stack(..),
  stack_var_lookup,
  is_visited,
  make_stack_key,
  make_thread_key,
  union_sym_tables,
  ReduceSyms(..),
  append_rs_writes,
  SymApp(..),
  PatMatchSyms(..),
  append_pms_writes,
  Pipe,
  is_zeroth_kind,
  to_expr,
  expr_map,
  runIO_expr
) where


import GHC
import Var ( varName, varType )
import Type ( eqType )
import Outputable (showPpr)

-- for runIO# synthesis
import Name ( mkSystemName )
import OccName ( mkVarOcc )
import Unique ( mkVarOccUnique )
import FastString ( mkFastString ) 
import Var ( mkLocalVar )
import IdInfo ( vanillaIdInfo, IdDetails(VanillaId) )

import Data.Tuple.Extra ( second, both, (***), (&&&) )
import Data.Coerce ( coerce )
import Data.Map.Strict ( Map(..), empty, union, unionWith, unionsWith, toList, fromList, (!?), filterWithKey, elems )
import qualified Data.Map.Strict as M ( map )
import Data.Set ( Set(..) )
import Data.Semigroup ( Semigroup(..), (<>) )
import Data.Monoid ( Monoid(..), mempty, mconcat )
import Data.Maybe ( listToMaybe )
import Control.Applicative ( (<|>) )
import Control.Exception ( assert )

import Ra.Extra ( update_head, zipAll )

-- Note about making SymTables from bindings: `Fun` needs to be lifted to `HsExpr` through the `HsLam` constructor. This is to unify the type of the binding to `HsExpr` while retaining MatchGroup which is necessary at HsApp on a named function.

-- class Symbol s where
--   mksym :: HsExpr GhcTc -> s
--   unsym :: s -> HsExpr GhcTc -- this seems really unidiomatic

-- instance Symbol Sym where
--   mksym = id
--   unsym = id

-- instance ReduceSyms 

data Sym = Sym {
  is_consumed :: Bool, -- usually Bool for whether it's consumer-passed
  stack_loc :: StackKey,
  expr :: LHsExpr GhcTc
}
expr_map :: (LHsExpr GhcTc -> LHsExpr GhcTc) -> Sym -> Sym
expr_map f sym = sym {
    expr = f $ expr sym
  }
  
type SymTable = Map Id [SymApp] -- the list is of a symbol table for partial function apps, and the expression.
union_sym_tables = unionsWith (++)
-- ah crap, lambdas. these only apply to IIFEs, but still a pain.

type StackKey = [SrcSpan]
type ThreadKey = StackKey -- ThreadKey is specialized so only the stack above the latest forkIO call is included
type Writes = Map Pipe [(ThreadKey, SymApp)]
type Pipe = (Id, ThreadKey) -- LHsExpr GhcTc

data SymApp = SA {
  sa_sym :: Sym,
  sa_args :: [[SymApp]]
} -- 2D tree. Too bad we can't use Tree; the semantics are totally different
data ReduceSyms = ReduceSyms {
  rs_syms :: [SymApp], -- fun-args forms
  rs_writes :: Writes
}
append_rs_writes :: Writes -> ReduceSyms -> ReduceSyms
append_rs_writes w rs = rs { rs_writes = rs_writes rs <> w }

data PatMatchSyms = PatMatchSyms {
  pms_syms :: SymTable,
  pms_writes :: Writes
}
append_pms_writes :: Writes -> PatMatchSyms -> PatMatchSyms
append_pms_writes w pms = pms { pms_writes = pms_writes pms <> w }

-- type StackTable = SetTree StackFrame -- One entry for every level deep and every invokation in a stack frame, so separate invokations of the same function can be distinguished
newtype StackBranch = SB [(SrcSpan, SymTable)] -- nodes: consecutive ones are child-parent
unSB (SB v) = v
mapSB f = SB . f . unSB

data Stack = Stack {
  st_branch :: StackBranch,
  st_threads :: [Int]
}

instance Semigroup StackBranch where
  (<>) =
    let combine (Just (a_src, a_table)) (Just b@(b_src, b_table)) = assert (a_src == b_src) (second (union_sym_tables . (:[a_table])) b) -- prefer first (accumulating) branch
        combine Nothing (Just b) = b
        combine (Just a) Nothing = a
    in curry $ SB . map (uncurry combine) . uncurry zipAll . both unSB

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
is_zeroth_kind sym = case unLoc $ expr sym of
  HsLit _ _ -> True
  HsOverLit _ _ -> True
  ExplicitTuple _ _ _ -> True
  ExplicitList _ _ _ -> True
  _ -> False

to_expr :: Sym -> HsExpr GhcTc
to_expr = unLoc . expr

make_thread_key :: Stack -> ThreadKey
make_thread_key stack =
  if not $ null $ st_threads stack
    then drop ((length $ unSB $ st_branch stack) - (head $ st_threads stack)) $ make_stack_key stack
    else mempty

make_stack_key :: Stack -> StackKey
make_stack_key = map fst . unSB . st_branch

stack_var_lookup :: Bool -> Id -> Stack -> Maybe [SymApp]
stack_var_lookup soft v = branch_var_lookup soft v . st_branch

branch_var_lookup :: Bool -> Id -> StackBranch -> Maybe [SymApp]
branch_var_lookup soft v = foldr ((\t -> (<|>(pick t))) . snd) Nothing . unSB  -- for some reason, `coerce` doesn't want to work here from some ambiguity that I can't understand
  where pick = if soft
          then listToMaybe . elems . filterWithKey (const . uncurry (&&) . ((==(varName v)) . varName &&& (eqType (varType v)) . varType))
          else (!?v)

is_visited :: Stack -> SrcSpan -> Bool
is_visited = flip elem . map fst . unSB . st_branch

clear_branch :: StackBranch -> StackBranch
clear_branch = SB . map (second (const empty)) . unSB

update_head_table :: SymTable -> StackBranch -> StackBranch
update_head_table next_table = SB . update_head (second (uncurry (<>) . (,next_table))) . unSB

union_branches :: [StackBranch] -> StackBranch
union_branches = mconcat

runIO_name :: Name
runIO_name = mkSystemName (mkVarOccUnique $ mkFastString "runIO#") (mkVarOcc "runIO#")
runIO_expr :: LHsExpr GhcTc
runIO_expr = undefined -- HsVar $ noLoc $ mkLocalVar VanillaId runIO_name (error "Boilerplate to write runIO#'s type in GHC-land not yet written") vanillaIdInfo
-- union_sym_tables :: [SymTable] -> SymTable
-- union_sym_tables = unionsWith (++) . map coerce -- TODO check if we need to be more sophisticated than this crude merge