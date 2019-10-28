{-# LANGUAGE TupleSections, DeriveFunctor, LambdaCase, NamedFieldPuns #-}
module Ra.Lang (
  Sym(..),
  SymTable(..),
  StackBranch(..),
  StackKey,
  ThreadKey(..),
  StackFrame(..),
  unSB,
  mapSB,
  Stack(..),
  stack_var_lookup,
  make_stack_key,
  make_thread_key,
  var_ref_tail,
  update_head_table,
  append_frame,
  ReduceSyms(..),
  PatMatchSyms(..),
  append_pms_writes,
  append_rs_writes,
  pms2rs,
  lift_rs_syms2,
  SymApp(..),
  Write(..),
  Writes(..),
  Hold(..),
  Pipe,
  Binds,
  ReduceStateMachine(..),
  is_parent,
  is_visited,
  is_zeroth_kind,
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
import Data.Maybe ( listToMaybe, catMaybes )
import Control.Applicative ( (<|>) )
import Control.Exception ( assert )

import Ra.Extra ( update_head, zipAll )

-- Note about making SymTables from bindings: `Fun` needs to be lifted to `HsExpr` through the `HsLam` constructor. This is to unify the type of the binding to `HsExpr` while retaining MatchGroup which is necessary at HsApp on a named function.

type Sym = LHsExpr GhcTc
-- instance Eq Sym where
--   (Sym loc1 _) == (Sym loc2 _) = loc1 == loc2
-- instance Ord Sym where
--   (Sym loc1 _) <= (Sym loc2 _) = loc1 <= loc2

-- expr_map :: (LHsExpr GhcTc -> LHsExpr GhcTc) -> Sym -> Sym
-- expr_map f sym = sym {
--     expr = f $ expr sym
--   }
  
type Binds = [(Pat GhcTc, ReduceSyms)]
data SymTable = SymTable {
  stbl_table :: Map Id [SymApp], -- strictly speaking, binds => table always, but it's so expensive both performance-wise and in code, so memoization does something good here
  stbl_binds :: Binds
}

instance Semigroup SymTable where
  (SymTable ltbl lbinds) <> (SymTable rtbl rbinds) = SymTable (unionWith (++) ltbl rtbl) (lbinds <> rbinds)

instance Monoid SymTable where
  mempty = SymTable mempty mempty
  mappend = (<>)

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
  sa_stack :: Stack,
    -- laws for `consumers`:
    -- 1. if a term is consumed and decomposed or part of an unknown/partial application, the whole term is consumed under the same consumer[s]
    -- 2. if a term goes through multiple consumers, they're all tracked for races individually
  sa_sym :: Sym,
  sa_args :: [[SymApp]]
} -- 2D tree. Too bad we can't use Tree; the semantics are totally different

instance Eq SymApp where
  (==) = curry $ flip all preds . flip ($) where
    preds = [
        uncurry (==) . both sa_args,
        uncurry (==) . both (st_branch . sa_stack),
        uncurry (==) . both (getLoc . sa_sym)
      ]
    

data Hold = Hold {
  h_pat :: Pat GhcTc,
  h_sym :: SymApp
}

data PatMatchSyms = PatMatchSyms {
  pms_syms :: SymTable,
  pms_writes :: Writes
}
data ReduceSyms = ReduceSyms {
  rs_syms :: [SymApp],
  rs_writes :: Writes
}

lift_rs_syms2 :: ([SymApp] -> [SymApp] -> [SymApp]) -> ReduceSyms -> ReduceSyms -> ReduceSyms
lift_rs_syms2 f a b = (a <> b) {
  rs_syms = f (rs_syms a) (rs_syms b)
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
pms2rs pms = ReduceSyms {
  rs_syms = concat $ elems $ stbl_table $ pms_syms pms,
  rs_writes = pms_writes pms
}

data StackFrame = VarRefFrame Id | AppFrame {
  af_raw :: SymApp, -- for anti-cycle purposes
  af_syms :: SymTable
}

-- BOOKMARK: Stack needs to be oufitted with the graph of bindings that refer to each other, in case a hold resolves and a new pattern match works.

newtype StackBranch = SB [StackFrame] -- TODO flatten this to type alias -- nodes: consecutive ones are child-parent
unSB (SB v) = v
mapSB f = SB . f . unSB
  
-- instance Ord StackBranch where
--   (<=) = (curry $ uncurry (<=) . both (map fst . unSB))

instance Eq StackBranch where
  (==) = curry $ uncurry (&&) . (
      uncurry (==) . both length
      &&& all (uncurry pred) . uncurry zip
    ) . both unSB where
    pred (AppFrame { af_raw = l }) (AppFrame { af_raw = r }) = (getLoc $ sa_sym l) == (getLoc $ sa_sym r) -- don't push the equality recursion any further
    pred (VarRefFrame l) (VarRefFrame r) = l == r
    pred _ _ = False

is_parent = undefined
-- is_parent p q = SB (take (length (unSB q)) (unSB p)) == q

is_visited :: StackBranch -> SymApp -> Bool
is_visited sb sa = any (\case
    AppFrame { af_raw } -> af_raw == sa
    _ -> False
  ) (unSB sb)

instance Semigroup StackBranch where
  (<>) =
    let combine (Just a) (Just b) = assert (af_raw a == af_raw b) (a {
            af_syms = (af_syms a <> af_syms b)
          }) -- prefer first (accumulating) branch
        combine Nothing (Just b) = b
        combine (Just a) Nothing = a
    in curry $ SB . map (uncurry combine) . uncurry zipAll . both unSB

instance Monoid StackBranch where
  mempty = SB mempty
  mappend = (<>)

data Stack = Stack {
  st_branch :: StackBranch,
  st_thread :: (StackBranch, StackBranch) -- stack of forkIO and stack of thing being forked resp.; this pair is unique if the anti-cycle works properly
}

-- instance Eq Stack where
--   l == r = st_branch l == st_branch r -- disregard thread for anti-cycle purposes

-- instance Semigroup Stack where
--   (Stack b_l t_l) <> (Stack b_r t_r) = Stack (b_l <> b_r) (t_l <> t_r)

-- instance Monoid Stack where
--   mempty = Stack mempty mempty
--   mappend = (<>)

instance Semigroup ReduceSyms where
  (ReduceSyms lsyms lwrites) <> (ReduceSyms rsyms  rwrites) = ReduceSyms (lsyms <> rsyms) (unionWith (++) lwrites rwrites) -- is there a nicer way to do this?
  
  -- vs. (<>) = curry $ uncurry ReduceSyms . ((uncurry (++) . fmap rs_syms) &&& (uncurry (unionWith (++)) . fmap ss_syms))

instance Monoid ReduceSyms where
  mempty = ReduceSyms mempty mempty
  mappend = (<>)


instance Semigroup PatMatchSyms where
  (PatMatchSyms lsyms lwrites) <> (PatMatchSyms rsyms rwrites) = PatMatchSyms (lsyms <> rsyms) (unionWith (++) lwrites rwrites)
  
instance Monoid PatMatchSyms where
  mempty = PatMatchSyms mempty mempty
  mappend = (<>)
  
data ReduceStateMachine = RSM {
  -- rs_writes :: Set StackKey,
  -- rs_holds :: Set StackKey,
  rsm_stacks :: [Stack], -- extra bit of state for memoization and to enable stop condition
  rsm_syms :: ReduceSyms -- the magic hat we're pulling all the rabbits out of; a 2-stack for new and old (resp.), so that we can have a halt condition based on the number of new writes (when the left is a subset of the right, we're done)
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
is_zeroth_kind sym = case unLoc sym of
  HsLit _ _ -> True
  HsOverLit _ _ -> True
  ExplicitTuple _ _ _ -> True
  ExplicitList _ _ _ -> True
  _ -> False

make_thread_key :: Stack -> ThreadKey
make_thread_key stack = undefined {- TKNormal $
  if not $ null $ st_thread stack
    then drop ((length $ unSB $ st_branch stack) - (head $ st_thread stack)) $ make_stack_key stack
    else mempty -}

make_stack_key :: Stack -> StackKey
make_stack_key = catMaybes . map (\case
    AppFrame { af_raw } -> Just $ getLoc $ sa_sym af_raw
    VarRefFrame _ -> Nothing
  ) . unSB . st_branch -- map fst . unSB . st_branch

-- var_ref_tail used for the law that var resolution cycles only apply to the tail
var_ref_tail :: Stack -> [Id]
var_ref_tail = var_ref_tail' . unSB . st_branch where
  var_ref_tail' ((VarRefFrame v):rest) = v:(var_ref_tail' rest)
  var_ref_tail' _ = []

stack_var_lookup :: Bool -> Id -> Stack -> Maybe [SymApp]
stack_var_lookup soft v = branch_var_lookup soft v . st_branch

branch_var_lookup :: Bool -> Id -> StackBranch -> Maybe [SymApp]
branch_var_lookup soft v = foldr (\case
    AppFrame { af_syms } -> (<|>(pick $ stbl_table af_syms))
    _ -> id
  ) Nothing . unSB where
    pick = if soft
      then listToMaybe . elems . filterWithKey (const . uncurry (&&) . ((==(varName v)) . varName &&& (eqType (varType v)) . varType))
      else (!?v)

update_head_table :: SymTable -> Stack -> Stack
update_head_table next_table st = undefined {- st {
  st_branch = SB $ update_head (second (uncurry (<>) . (,next_table))) $ unSB $ st_branch st
} -}

append_frame :: StackFrame -> Stack -> Stack
append_frame frame stack = stack {
  st_branch = SB (frame : (coerce $ st_branch stack))
}

union_branches :: [StackBranch] -> StackBranch
union_branches = mconcat

runIO_name :: Name
runIO_name = mkSystemName (mkVarOccUnique $ mkFastString "runIO#") (mkVarOcc "runIO#")
runIO_expr :: LHsExpr GhcTc
runIO_expr = undefined -- HsVar $ noLoc $ mkLocalVar VanillaId runIO_name (error "Boilerplate to write runIO#'s type in GHC-land not yet written") vanillaIdInfo
-- union_sym_tables :: [SymTable] -> SymTable
-- union_sym_tables = unionsWith (++) . map coerce -- TODO check if we need to be more sophisticated than this crude merge