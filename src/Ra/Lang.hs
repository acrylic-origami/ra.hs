{-# LANGUAGE TupleSections, DeriveFunctor, UndecidableInstances #-}
module Ra.Lang (
  Sym(..),
  SymTable(..),
  StackBranch(..),
  StackKey,
  ThreadKey(..),
  unSB,
  mapSB,
  Stack(..),
  stack_var_lookup,
  is_visited,
  make_stack_key,
  make_thread_key,
  union_sym_tables,
  update_head_table,
  ReduceSyms(..),
  PatMatchSyms(..),
  append_pms_writes,
  append_rs_writes,
  SymApp(..),
  Write(..),
  Writes(..),
  Hold(..),
  Pipe,
  ReduceStateMachine(..),
  is_parent,
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
  stack_loc :: StackKey,
  expr :: LHsExpr GhcTc
}
instance Eq Sym where
  (Sym loc1 _) == (Sym loc2 _) = loc1 == loc2
instance Ord Sym where
  (Sym loc1 _) <= (Sym loc2 _) = loc1 <= loc2

expr_map :: (LHsExpr GhcTc -> LHsExpr GhcTc) -> Sym -> Sym
expr_map f sym = sym {
    expr = f $ expr sym
  }
  
type SymTable = Map Id [SymApp] -- the list is of a symbol table for partial function apps, and the expression.
union_sym_tables = unionsWith (++)
-- ah crap, lambdas. these only apply to IIFEs, but still a pain.

type StackKey = [SrcSpan]
data ThreadKey = TKNormal StackKey | TKEnemy -- ThreadKey is specialized so only the stack above the latest forkIO call is included
data Write = Write {
  w_stack :: Stack,
  w_sym :: SymApp
} -- ThreadKey for the thread the write happens, StackKey for dedupeing writes in the top-level state machine

-- Write instances allowing them to be keys
-- instance Eq Write where
--   (Write l_stack _) == (Write r_stack _) = l_loc == r_loc

-- instance Ord Write where
--   (Write l_stack _) <= (Write r_stack _) = l_loc <= r_loc
  
type Writes = Map Pipe [Write]
type Pipe = StackKey -- LHsExpr GhcTc

data SymApp = SA {
  sa_consumers :: [StackKey],
    -- laws for `consumers`:
    -- 1. if a term is consumed and decomposed or part of an unknown/partial application, the whole term is consumed under the same consumer[s]
    -- 2. if a term goes through multiple consumers, they're all tracked for races individually
  sa_sym :: Sym,
  sa_args :: [[SymApp]]
} -- 2D tree. Too bad we can't use Tree; the semantics are totally different
data Hold = Hold {
  h_pat :: Pat GhcTc,
  h_sym :: SymApp,
  h_stack :: Stack
}

data PatMatchSyms = PatMatchSyms {
  pms_syms :: SymTable,
  pms_holds :: [Hold],
  pms_writes :: Writes
}
data ReduceSyms = ReduceSyms {
  rs_syms :: [SymApp],
  rs_holds :: [Hold],
  rs_writes :: Writes
}

-- data Syms t = Syms {
--   ss_syms :: t SymApp,
--   ss_holds :: [Hold],
--   ss_writes :: Writes
-- }
-- type ReduceSyms = Syms []
-- type PatMatchSyms = Syms (Map Id) -- can't use SymTable because partially-applied type synonyms are illegal. This trouble to keep Syms generalized is getting very close to impractical

append_rs_writes ws rs = rs {
  rs_writes = unionWith (++) (rs_writes rs) ws
}
append_pms_writes ws pms = pms {
  pms_writes = unionWith (++) (pms_writes pms) ws
}

newtype StackBranch = SB [(SrcSpan, SymTable)] -- nodes: consecutive ones are child-parent
unSB (SB v) = v
mapSB f = SB . f . unSB

instance Eq StackBranch where
  (==) = (curry $ uncurry (==) . both (map fst . unSB))
  
instance Ord StackBranch where
  (<=) = (curry $ uncurry (<=) . both (map fst . unSB))

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
  (ReduceSyms lsyms lholds lwrites) <> (ReduceSyms rsyms rholds rwrites) = ReduceSyms (lsyms <> rsyms) (lholds <> rholds) (unionWith (++) lwrites rwrites) -- is there a nicer way to do this?
  
  -- vs. (<>) = curry $ uncurry ReduceSyms . ((uncurry (++) . fmap rs_syms) &&& (uncurry (unionWith (++)) . fmap ss_syms))

instance Monoid ReduceSyms where
  mempty = ReduceSyms mempty mempty mempty
  mappend = (<>)


instance Semigroup PatMatchSyms where
  (PatMatchSyms lsyms lholds lwrites) <> (PatMatchSyms rsyms rholds rwrites) = PatMatchSyms (unionWith (++) lsyms rsyms) (lholds <> rholds) (unionWith (++) lwrites rwrites)
  
instance Monoid PatMatchSyms where
  mempty = PatMatchSyms mempty mempty mempty
  mappend = (<>)
  
data ReduceStateMachine = RSM {
  -- rs_writes :: Set StackKey,
  -- rs_holds :: Set StackKey,
  rsm_stacks :: [Stack], -- extra bit of state for memoization and to enable stop condition
  rsm_syms :: (ReduceSyms, ReduceSyms) -- the magic hat we're pulling all the rabbits out of; a 2-stack for new and old (resp.), so that we can have a halt condition based on the number of new writes (when the left is a subset of the right, we're done)
}

instance Semigroup ReduceStateMachine where
  (RSM l_stacks l_syms) <> (RSM r_stacks r_syms) =
      RSM
        (l_stacks <> r_stacks)
        (l_syms <> r_syms)
  
instance Monoid ReduceStateMachine where
  mempty = RSM mempty mempty
  mappend = (<>)
  
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
make_thread_key stack = TKNormal $
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

is_parent :: StackBranch -> StackBranch -> Bool
is_parent = curry $ uncurry (&&) . (
    uncurry (<) . both length
    &&& and . map (uncurry (==) . both fst) . uncurry zip
  ) . both unSB

clear_branch :: StackBranch -> StackBranch
clear_branch = SB . map (second (const empty)) . unSB

update_head_table :: SymTable -> Stack -> Stack
update_head_table next_table st = st {
  st_branch = SB $ update_head (second (uncurry (<>) . (,next_table))) $ unSB $ st_branch st
}

union_branches :: [StackBranch] -> StackBranch
union_branches = mconcat

runIO_name :: Name
runIO_name = mkSystemName (mkVarOccUnique $ mkFastString "runIO#") (mkVarOcc "runIO#")
runIO_expr :: LHsExpr GhcTc
runIO_expr = undefined -- HsVar $ noLoc $ mkLocalVar VanillaId runIO_name (error "Boilerplate to write runIO#'s type in GHC-land not yet written") vanillaIdInfo
-- union_sym_tables :: [SymTable] -> SymTable
-- union_sym_tables = unionsWith (++) . map coerce -- TODO check if we need to be more sophisticated than this crude merge