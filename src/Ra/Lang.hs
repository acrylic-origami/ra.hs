{-# LANGUAGE Rank2Types, TupleSections, DeriveFunctor, DeriveDataTypeable, LambdaCase, NamedFieldPuns #-}
module Ra.Lang (
  Sym(..),
  getSymLoc,
  setSymLoc,
  LUT,
  Lookup,
  SymTable(..),
  Stack(..),
  StackKey,
  -- ThreadKey(..),
  StackFrame(..),
  stack_eq,
  stack_var_lookup,
  soft_table_lookup,
  make_loc_key,
  -- make_thread_key,
  stack_apps,
  is_monadic,
  update_head_table,
  ReduceSyms(..),
  PatMatchSyms(..),
  append_pms_stmts,
  append_rs_stmts,
  pms2rs,
  lift_rs_syms2,
  SymApp(..),
  sa_from_sym,
  sub_sa_types_T,
  sub_sa_types_wo_stack,
  Write,
  Writes(..),
  DoStmt(..),
  -- Hold(..),
  Pipe,
  Bind,
  ReduceStateMachine(..),
  is_visited,
  is_parent,
  is_zeroth_kind,
  runIO_expr
) where

import GHC
import Var ( varName, varType, setVarType )
import Type ( mkFunTys, mkAppTy, mkAppTys, getTyVar_maybe, dropForAlls )
import TyCon ( tyConName )

-- for WildPat synthesis
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
import Control.Arrow ( first, second, (***), (&&&) )
import Control.Monad ( join )
import Data.Coerce ( coerce )
import Data.Map.Strict ( Map(..), empty, union, unionWith, unionsWith, toList, fromList, (!?), filterWithKey, elems )
import qualified Data.Map.Strict as M ( map )
import Data.Generics ( everywhere, everywhereBut, everything, GenericT, extT, mkT, mkQ )
import Data.Set ( Set(..) )
import Data.Semigroup ( Semigroup(..), (<>) )
import Data.Monoid ( Monoid(..), mempty, mconcat )
import Data.Maybe ( listToMaybe, catMaybes, isJust, fromMaybe )
import Control.Applicative ( (<|>), liftA2 )
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

setSymLoc sym loc = case sym of
  (Sym (L _ s)) -> Sym (L loc s)
  (TupleConstr _) -> TupleConstr loc
  (ListConstr _) -> ListConstr loc
  EntryPoint -> EntryPoint

instance Eq Sym where
  l == r = getSymLoc l == getSymLoc r
  
-- instance Ord Sym where
--   (Sym loc1 _) <= (Sym loc2 _) = loc1 <= loc2

-- expr_map :: (LHsExpr GhcTc -> LHsExpr GhcTc) -> Sym -> Sym
-- expr_map f sym = sym {
--     expr = f $ expr sym
--   }
  
type Bind = (LPat GhcTc, [SymApp])
type LUT = Map Id [SymApp]
data SymTable = SymTable {
  stbl_table :: LUT, -- strictly speaking, binds => table always, but it's so expensive both performance-wise and in code, so memoization does something good here
  stbl_binds :: [Bind]
}
  deriving (Data, Typeable)

type Lookup = LUT -> Id -> Maybe [SymApp]

instance Semigroup SymTable where
  (SymTable ltbl lbinds) <> (SymTable rtbl rbinds) = SymTable (unionWith (++) ltbl rtbl) (lbinds <> rbinds)

instance Monoid SymTable where
  mempty = SymTable mempty mempty
  mappend = (<>)

type StackKey = [SrcSpan]
type Thread = SymApp
-- data ThreadKey = TKNormal StackKey | TKEnemy -- ThreadKey is specialized so only the stack above the latest forkIO call is included
type Write = ([Pipe], [SymApp])

-- Write instances allowing them to be keys
-- instance Eq Write where
--   (Write l_stack _) == (Write r_stack _) = l_loc == r_loc

-- instance Ord Write where
--   (Write l_stack _) <= (Write r_stack _) = l_loc <= r_loc
  
type Writes = [Write] -- TODO not my prettiest kludge: this went from unique pipe to many writes (in a Map) to non-unique pipe to many writes (`[(Pipe, [Write])]`) to this: a free-for-all relationship. All to allow `pat_match` to be generic.
type DoStmt = SymApp
type Pipe = SymApp -- LHsExpr GhcTc

data SymApp = SA {
  sa_consumers :: [StackKey],
  sa_loc :: Stack,
  sa_stack :: Stack,
    -- laws for `consumers`:
    -- 1. if a term is consumed and decomposed or part of an unknown/partial application, the whole term is consumed under the same consumer[s]
    -- 2. if a term goes through multiple consumers, they're all tracked for races individually
  sa_sym :: Sym,
  sa_args :: [[SymApp]],
  sa_thread :: Maybe SymApp -- TODO consider a more elegant type
} deriving (Data, Typeable) -- 2D tree. Too bad we can't use Tree; the semantics are totally different

sa_from_sym s = SA mempty mempty mempty s mempty Nothing

get_sa_type :: SymApp -> Type -- FYI this is the type _after_ reduction; i.e. apps and sections go down an arity, OpApps go down two. The law: this preserves types of all terminal symbols (see HsLam[Case], HsVar, Hs[Over]Lit, ExplicitTuple, ExplicitList)
get_sa_type sa =
  case sa_sym sa of
    Sym expr -> get_expr_type expr
    TupleConstr _ -> mkAppTys (error "Report this bug: too lazy to make actual Tuple TyCon.") (map (get_sa_type . head) (sa_args sa))
    ListConstr _ -> mkAppTy (error "Report this bug: too lazy to make actual list TyCon.") (get_sa_type $ head $ head $ sa_args sa)
    EntryPoint -> error "Tried to get the type of EntryPoint"

sub_sa_types_T :: SymApp -> GenericT
sub_sa_types_T sa =
  let (sa_fun_args, sa_fun_ret_ty) = splitFunTysLossy $ everywhere (mkT dropForAlls) $ get_sa_type sa
      type_map = mconcat $ map (fromMaybe mempty . join . uncurry (liftA2 inst_subty) . (fmap reduce_types . listToMaybe *** pure)) (zip (sa_args sa) sa_fun_args) -- beta-reduce all types in the left-hand sides -- account for possibly missing arguments (due to anti-cycle) -- expect # sa_fun_tys > sa_args 
      tx :: GenericT
      tx = mkT (uncurry fromMaybe . (id &&& join . fmap (type_map!?) . getTyVar_maybe))
  in snd (sa, tx `extT` (\v -> (setVarType v $ everywhere tx $ varType v)))

sub_sa_types_wo_stack :: SymApp -> GenericT
sub_sa_types_wo_stack sa = everywhereBut (False `mkQ` (const True :: Stack -> Bool)) (sub_sa_types_T sa)
  
reduce_types :: SymApp -> Type
reduce_types sa = uncurry mkFunTys $ everywhere (sub_sa_types_T sa) $ first (drop (length $ sa_args sa)) $ splitFunTysLossy $ get_sa_type sa
  
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

data StackFrame =
  EmptyFrame
  | AppFrame {
    af_raw :: SymApp, -- for anti-cycle purposes
    af_syms :: SymTable
  }
  | BindFrame {
    bf_syms :: SymTable
  }
  | StmtFrame
  deriving (Data, Typeable)

-- BOOKMARK: Stack needs to be oufitted with the graph of bindings that refer to each other, in case a hold resolves and a new pattern match works.

type Stack = [StackFrame] -- TODO flatten this to type alias -- nodes: consecutive ones are child-parent

-- instance Ord Stack where
--   (<=) = (curry $ uncurry (<=) . both (map fst . unSB))

stack_eq = curry $ uncurry (&&) . (
    uncurry (==) . both length
    &&& all (uncurry (==) . both (getSymLoc . sa_sym . af_raw)) . uncurry zip
  ) . both stack_apps

is_parent = curry $ (\(p, q) -> take (length q) p `stack_eq` q) . both stack_apps

is_visited :: Stack -> SymApp -> Bool
is_visited sb sa = any (\case
    AppFrame { af_raw } -> (sa_sym af_raw) == (sa_sym sa)
    _ -> False
  ) sb


-- instance Semigroup Stack where
--   (<>) =
--     let combine (Just a) (Just b) = assert (af_raw a == af_raw b) (a {
--             af_syms = (af_syms a <> af_syms b)
--           }) -- prefer first (accumulating) stack
--         combine Nothing (Just b) = b
--         combine (Just a) Nothing = a
--     in curry $ SB . map (uncurry combine) . uncurry zipAll

-- instance Monoid Stack where
--   mempty = SB mempty
--   mappend = (<>)

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
    then drop ((length stack) - (head $ st_thread stack)) $ make_loc_key stack
    else mempty -}

make_loc_key :: SymApp -> StackKey
make_loc_key = uncurry (:) . (
    getSymLoc . sa_sym
    &&& catMaybes . map (\case
        AppFrame { af_raw } -> Just $ getSymLoc $ sa_sym af_raw
        _ -> Nothing
      ) . sa_loc -- map fst
  )

stack_apps :: Stack -> [StackFrame]
stack_apps = filter (\case { AppFrame {} -> True; _ -> False })

is_monadic :: Stack -> Bool
is_monadic (AppFrame{}:_) = False
is_monadic (StmtFrame:_) = True
is_monadic (_:rest) = is_monadic rest
is_monadic [] = False

-- stack_var_refs used for the law that var resolution cycles only apply to the tail
-- stack_var_refs :: Stack -> [Id]
-- stack_var_refs ((VarRefFrame v):rest) = v:(stack_var_refs' rest)
-- stack_var_refs _ = []

soft_table_lookup :: Lookup
soft_table_lookup tbl v = listToMaybe $ elems $ filterWithKey (\q ->
    const $ uncurry (&&) $ (
        (==(varString v)) . varString -- const True
        &&& isJust . inst_subty (varType v) . varType
      ) q -- DEBUG
  ) tbl

stack_var_lookup :: Stack -> Id -> Maybe [SymApp]
stack_var_lookup st v =
  let folder syms = uncurry ($) . first ((<|>) . ($(stbl_table syms)))
  in snd $ foldr (
      (((!?v),).)
      . (\case
          AppFrame { af_syms } -> folder af_syms
          BindFrame { bf_syms } -> folder bf_syms
          _ -> snd
        )
    )
    ((`soft_table_lookup` v), Nothing)
    st

update_head_table :: SymTable -> Stack -> Stack
update_head_table next_table st = undefined {- update_head (second (uncurry (<>) . (,next_table))) st
} -}

runIO_name :: Name
runIO_name = mkSystemName (mkVarOccUnique $ mkFastString "runIO#") (mkVarOcc "runIO#")
runIO_expr :: LHsExpr GhcTc
runIO_expr = undefined -- HsVar $ 
-- union_sym_tables :: [SymTable] -> SymTable
-- union_sym_tables = unionsWith (++) . map coerce -- TODO check if we need to be more sophisticated than this crude merge