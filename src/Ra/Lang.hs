{-# LANGUAGE TupleSections, DeriveFunctor, DeriveDataTypeable, LambdaCase, NamedFieldPuns #-}
module Ra.Lang (
  Sym(..),
  getSymLoc,
  SymTable(..),
  Stack(..),
  StackKey,
  -- ThreadKey(..),
  StackFrame(..),
  unSB,
  mapSB,
  stack_var_lookup,
  table_lookup,
  make_stack_key,
  -- make_thread_key,
  stack_apps,
  stack_var_refs,
  update_head_table,
  ReduceSyms(..),
  PatMatchSyms(..),
  append_pms_stmts,
  append_rs_stmts,
  pms2rs,
  lift_rs_syms2,
  SymApp(..),
  sa_from_sym,
  Write,
  Writes(..),
  DoStmt(..),
  -- Hold(..),
  Pipe,
  Bind,
  ReduceStateMachine(..),
  is_parent,
  is_zeroth_kind,
  runIO_expr
) where

import GHC
import Var ( varName, varType )
import Type ( eqType )
import qualified Pretty ( empty, text )
import Outputable ( showPpr, Outputable(..), docToSDoc )

-- for runIO# synthesis
import Name ( mkSystemName )
import OccName ( mkVarOcc )
import Unique ( mkVarOccUnique )
import FastString ( mkFastString ) 
import Var ( mkLocalVar )
import IdInfo ( vanillaIdInfo, IdDetails(VanillaId) )

import Data.Data ( Data(..), Typeable(..) )
import Control.Arrow ( second, (***), (&&&) )
import Data.Coerce ( coerce )
import Data.Map.Strict ( Map(..), empty, union, unionWith, unionsWith, toList, fromList, (!?), filterWithKey, elems )
import qualified Data.Map.Strict as M ( map )
import Data.Set ( Set(..) )
import Data.Semigroup ( Semigroup(..), (<>) )
import Data.Monoid ( Monoid(..), mempty, mconcat )
import Data.Maybe ( listToMaybe, catMaybes, isJust )
import Control.Applicative ( (<|>) )
import Control.Exception ( assert )

import Ra.Extra ( update_head, zipAll, both )
import Ra.GHC.Util

-- Note about making SymTables from bindings: `Fun` needs to be lifted to `HsExpr` through the `HsLam` constructor. This is to unify the type of the binding to `HsExpr` while retaining MatchGroup which is necessary at HsApp on a named function.

data Sym =
  Sym (LHsExpr GhcTc)
  | TupleConstr SrcSpan
  | ListConstr SrcSpan
  | EntryPoint
  deriving (Data, Typeable)

instance Outputable Sym where
  ppr (Sym v) = ppr v
  ppr (TupleConstr _) = docToSDoc (Pretty.text "()")
  ppr (ListConstr _) = docToSDoc (Pretty.text "[]")
  ppr EntryPoint = docToSDoc (Pretty.text "<<ENTRYPOINT>>")
  
  pprPrec r (Sym v) = pprPrec r v
  pprPrec _ (TupleConstr _) = docToSDoc (Pretty.text "()")
  pprPrec _ (ListConstr _) = docToSDoc (Pretty.text "[]")
  pprPrec _ EntryPoint = docToSDoc (Pretty.text "<<ENTRYPOINT>>")
  
getSymLoc (Sym v) = getLoc v
getSymLoc (TupleConstr l) = l
getSymLoc (ListConstr l) = l
getSymLoc EntryPoint = noSrcSpan

-- instance Eq Sym where
--   (Sym loc1 _) == (Sym loc2 _) = loc1 == loc2
-- instance Ord Sym where
--   (Sym loc1 _) <= (Sym loc2 _) = loc1 <= loc2

-- expr_map :: (LHsExpr GhcTc -> LHsExpr GhcTc) -> Sym -> Sym
-- expr_map f sym = sym {
--     expr = f $ expr sym
--   }
  
type Bind = (LPat GhcTc, [SymApp])
data SymTable = SymTable {
  stbl_table :: Map Id [SymApp], -- strictly speaking, binds => table always, but it's so expensive both performance-wise and in code, so memoization does something good here
  stbl_binds :: [Bind]
}
  deriving (Data, Typeable)

instance Semigroup SymTable where
  (SymTable ltbl lbinds) <> (SymTable rtbl rbinds) = SymTable (unionWith (++) ltbl rtbl) (lbinds <> rbinds)

instance Monoid SymTable where
  mempty = SymTable mempty mempty
  mappend = (<>)

type StackKey = [SrcSpan]
type Thread = SymApp
-- data ThreadKey = TKNormal StackKey | TKEnemy -- ThreadKey is specialized so only the stack above the latest forkIO call is included
type Write = SymApp

-- Write instances allowing them to be keys
-- instance Eq Write where
--   (Write l_stack _) == (Write r_stack _) = l_loc == r_loc

-- instance Ord Write where
--   (Write l_stack _) <= (Write r_stack _) = l_loc <= r_loc
  
type Writes = [([Pipe], [Write])] -- TODO not my prettiest kludge: this went from unique pipe to many writes (in a Map) to non-unique pipe to many writes (`[(Pipe, [Write])]`) to this: a free-for-all relationship. All to allow `pat_match` to be generic.
type DoStmt = SymApp
type Pipe = SymApp -- LHsExpr GhcTc

data SymApp = SA {
  sa_consumers :: [StackKey],
  sa_stack :: Stack,
    -- laws for `consumers`:
    -- 1. if a term is consumed and decomposed or part of an unknown/partial application, the whole term is consumed under the same consumer[s]
    -- 2. if a term goes through multiple consumers, they're all tracked for races individually
  sa_sym :: Sym,
  sa_args :: [[SymApp]],
  sa_thread :: Maybe SymApp -- TODO consider a more elegant type
} deriving (Data, Typeable) -- 2D tree. Too bad we can't use Tree; the semantics are totally different

sa_from_sym s = SA mempty mempty s mempty Nothing

-- instance Eq SymApp where
--   (==) = curry $ flip all preds . flip ($) where
--     preds = [
--         uncurry (==) . both sa_args,
--         uncurry (==) . both sa_stack,
--         uncurry (==) . both (getSymLoc . sa_sym)
--         -- uncurry (==) . both sa_thread -- I think a recursive call could keep spawning new threads of itself
--       ]

data PatMatchSyms = PatMatchSyms {
  pms_syms :: SymTable,
  pms_stmts :: [DoStmt]
} deriving (Data, Typeable)

data ReduceSyms = ReduceSyms {
  rs_syms :: [SymApp],
  rs_stmts :: [DoStmt]
} deriving (Data, Typeable)

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

append_rs_stmts ws rs = rs {
  rs_stmts = ws <> (rs_stmts rs)
}
append_pms_stmts ws pms = pms {
  pms_stmts = ws <> (pms_stmts pms)
}
pms2rs pms = ReduceSyms {
  rs_syms = concat $ elems $ stbl_table $ pms_syms pms,
  rs_stmts = pms_stmts pms
}

data StackFrame = EmptyFrame | VarRefFrame Id | AppFrame {
  af_raw :: SymApp, -- for anti-cycle purposes
  af_syms :: SymTable
} 
  deriving (Data, Typeable)

-- BOOKMARK: Stack needs to be oufitted with the graph of bindings that refer to each other, in case a hold resolves and a new pattern match works.

newtype Stack = SB [StackFrame] deriving (Data, Typeable) -- TODO flatten this to type alias -- nodes: consecutive ones are child-parent
unSB (SB v) = v
mapSB f = SB . f . unSB
  
-- instance Ord Stack where
--   (<=) = (curry $ uncurry (<=) . both (map fst . unSB))

instance Eq Stack where
  (==) = curry $ uncurry (&&) . (
      uncurry (==) . both length
      &&& all (uncurry pred) . uncurry zip
    ) . both unSB where
    pred (AppFrame { af_raw = l }) (AppFrame { af_raw = r }) = (getSymLoc $ sa_sym l) == (getSymLoc $ sa_sym r) -- don't push the equality recursion any further
    pred (VarRefFrame l) (VarRefFrame r) = l == r
    pred _ _ = False

is_parent = undefined
-- is_parent p q = SB (take (length (unSB q)) (unSB p)) == q

instance Semigroup Stack where
  (<>) =
    let combine (Just a) (Just b) = assert (af_raw a == af_raw b) (a {
            af_syms = (af_syms a <> af_syms b)
          }) -- prefer first (accumulating) stack
        combine Nothing (Just b) = b
        combine (Just a) Nothing = a
    in curry $ SB . map (uncurry combine) . uncurry zipAll . both unSB

instance Monoid Stack where
  mempty = SB mempty
  mappend = (<>)

instance Semigroup ReduceSyms where
  (ReduceSyms lsyms lstmts) <> (ReduceSyms rsyms  rstmts) = ReduceSyms (lsyms <> rsyms) (lstmts <> rstmts) -- is there a nicer way to do this?
  
  -- vs. (<>) = curry $ uncurry ReduceSyms . ((uncurry (++) . fmap rs_syms) &&& (uncurry (unionWith (++)) . fmap ss_syms))

instance Monoid ReduceSyms where
  mempty = ReduceSyms mempty mempty
  mappend = (<>)


instance Semigroup PatMatchSyms where
  (PatMatchSyms lsyms lstmts) <> (PatMatchSyms rsyms rstmts) = PatMatchSyms (lsyms <> rsyms) (lstmts <> rstmts)
  
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
is_zeroth_kind (Sym sym) = case unLoc sym of
  HsLit _ _ -> True
  HsOverLit _ _ -> True
  ExplicitTuple _ _ _ -> True
  ExplicitList _ _ _ -> True
  _ -> False
is_zeroth_kind _ = False

-- make_thread_key :: Stack -> ThreadKey
-- make_thread_key stack = undefined 
{- TKNormal $
  if not $ null $ st_thread stack
    then drop ((length $ unSB stack) - (head $ st_thread stack)) $ make_stack_key stack
    else mempty -}

make_stack_key :: SymApp -> StackKey
make_stack_key = uncurry (:) . (
    getSymLoc . sa_sym
    &&& catMaybes . map (\case
        AppFrame { af_raw } -> Just $ getSymLoc $ sa_sym af_raw
        _ -> Nothing
      ) . unSB . sa_stack -- map fst . unSB
  )

stack_apps :: Stack -> [StackFrame]
stack_apps = filter (\case { AppFrame {} -> True; _ -> False }) . unSB

stack_var_refs :: Stack -> [Id]
stack_var_refs = catMaybes . map (\case { VarRefFrame v -> Just v; _ -> Nothing }) . unSB

-- stack_var_refs used for the law that var resolution cycles only apply to the tail
-- stack_var_refs :: Stack -> [Id]
-- stack_var_refs = stack_var_refs' . unSB where
--   stack_var_refs' ((VarRefFrame v):rest) = v:(stack_var_refs' rest)
--   stack_var_refs' _ = []

table_lookup :: Id -> Map Id [SymApp] -> Maybe [SymApp]
table_lookup v tbl = uncurry (<|>) $ (
    (!?v)
    &&& listToMaybe . elems . filterWithKey (\q ->
        const $ uncurry (&&) $ (
            (==(varString v)) . varString
            &&& isJust . flip inst_subty (varType v) . varType
          ) q
      )
  ) tbl

stack_var_lookup :: Id -> Stack -> Maybe [SymApp]
stack_var_lookup v = foldr (\case
    AppFrame { af_syms } -> (<|>(table_lookup v (stbl_table af_syms)))
    _ -> id
  ) Nothing . unSB

update_head_table :: SymTable -> Stack -> Stack
update_head_table next_table st = undefined {- mapSB update_head (second (uncurry (<>) . (,next_table))) st
} -}

runIO_name :: Name
runIO_name = mkSystemName (mkVarOccUnique $ mkFastString "runIO#") (mkVarOcc "runIO#")
runIO_expr :: LHsExpr GhcTc
runIO_expr = undefined -- HsVar $ 
-- union_sym_tables :: [SymTable] -> SymTable
-- union_sym_tables = unionsWith (++) . map coerce -- TODO check if we need to be more sophisticated than this crude merge