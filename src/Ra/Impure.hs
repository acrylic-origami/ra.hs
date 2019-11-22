{-# LANGUAGE MultiWayIf, LambdaCase, NamedFieldPuns, TupleSections, DeriveDataTypeable #-}

module Ra.Impure (
  reduce,
  expand_reads
) where

import GHC

import Data.Maybe ( catMaybes )
import Data.Generics ( Data, Typeable )
import Data.Generics.Extra ( everywhereWithContextBut, mkQT, extQT )
import Control.Arrow ( (&&&), (***), first, second )

import Ra ( reduce_deep, pat_match )
import Ra.Lang
import Ra.Extra
import Ra.GHC.Util ( varString )

mk_write :: SymApp -> Maybe Write
mk_write sa | Sym (L _ (HsVar _ (L _ v))) <- sa_sym sa =
              if | varString v `elem` [
                    "writeIORef",
                    "writeSTRef",
                    "putMVar",
                    "writeTVar",
                    "tryPutMVar", -- <- TODO let somewhere else deal with the Bool that comes out
                    "atomicSwapIORef"
                  ]
                 , pipes:vals:_ <- sa_args sa
                 -> Just (pipes, vals)
                          
                 | varString v `elem` [
                    "newMVar", -- DEBUG
                    "newSTRef",
                    "newIORef",
                    "newTVar"
                  ]
                 , vals:_ <- sa_args sa
                 -> Just ([sa], vals) -- the "new__" expression itself is the pipe
                 
                 | varString v == "atomicModifyIORefLazy_" -- "atomicModifyIORef2Lazy" is todo: needs pattern matching
                 , pipes:fns:rest <- sa_args sa
                 -> Just (pipes, map (\sa' -> sa' {
                    sa_sym = TupleConstr noSrcSpan, -- TODO not very comfortable with noSrcSpan re: uniqueness
                    sa_args = [
                      pipes, -- old values
                      [ sa' {
                        sa_args = sa_args sa' <> [pipes] <> rest
                      } ] -- new values
                    ]
                  }) fns)
                 
                 | otherwise -> mempty
                 
             | otherwise = mempty


refresh_app_frames :: Stack -> (PatMatchSyms, Stack)
refresh_app_frames st = first mconcat $ unzip $ map (\frame -> case frame of
    AppFrame {} ->
      let next_pms = pat_match $ stbl_binds $ af_syms frame
      in (next_pms, frame {
        af_syms = pms_syms next_pms
      })
    _ -> (mempty, frame)
  ) st

unref :: Writes -> SymApp -> [SymApp]
unref ws sa =
  let bases = concatMap snd
        $ filter (
            (
                 -- beware of unLoc and conflicts between variables
                elem (getSymLoc $ sa_sym sa) . map (getSymLoc . sa_sym) -- TODO URGENT condition now too broad: need to account for shadowing
                -- &&& (elem (sa_loc sa)) . map sa_loc
              ) . fst
          ) ws -- by only taking `w_sym`, encode the law that write threads are not generally the threads that read (obvious saying it out loud, but it does _look_ like we're losing information here)
  in map (\sa' -> sa' {
      sa_args = sa_args sa' <> sa_args sa,
      sa_stack = (<>(sa_stack sa)) (sa_stack sa') -- NOTE another instance of substitution law: merge stacks
    }) bases


type WriteSite = (Stack, Stack) -- pipe and value locations
newtype Q a b = Q (Maybe (a, b)) deriving (Data, Typeable)
unQ (Q z) = z

permute2 = concatMap (\(pipes, syms) -> [(pipe, sym) | pipe <- pipes, sym <- syms]) -- TODO stopgap before implementing Map

reduce :: ReduceSyms -> [ReduceSyms]
reduce syms0 =
  let iterant :: [DoStmt] -> (Writes, ReduceSyms) -- always act on syms0, return what we get on this phase
      iterant stmts =
        let writes = catMaybes $ map mk_write stmts
            (next_stmts, next_rs) = everywhereWithContextBut (<>) (unQ . (
                (Q . Just . (mempty,))
                `mkQT` (Q . Just . (\sa ->
                    (mconcat *** concat)
                    $ unzip
                    $ map (\sa ->
                        let (next_pms, next_stack) = refresh_app_frames $ sa_stack sa -- re-pat-match the bindings 
                            next_rs = reduce_deep $ sa { sa_stack = next_stack }
                        in (
                            pms_stmts next_pms <> rs_stmts next_rs,
                            rs_syms next_rs
                          )
                      )
                    $ expand_reads writes sa
                  ))
                `extQT` (const (Q Nothing) :: Stack -> Q [DoStmt] Stack) -- TODO URGENT it is probably not correct to skip replacement into the stack: we also have to substitute bindings in there in case they need to match. However, the knotted table is going to be tricky: will need to totally reknot the table, which might be done by PMS?
              )) mempty syms0
        in (writes, next_rs {
          rs_stmts = rs_stmts next_rs <> next_stmts
        })
        
  in map snd
    $ head
    $ filter ((\(last_writes, next_rs) ->
        let next_writes_map = map (both sa_loc) $ permute2 $ catMaybes $ map mk_write $ rs_stmts next_rs
            last_writes_map = map (both sa_loc) $ permute2 last_writes
        in all ((`any` last_writes_map) . ((uncurry (&&)).) . uncurry (***) . both stack_eq) next_writes_map
      ) . head)
    $ iterate (\l -> (iterant $ rs_stmts $ snd $ head l):l) [(mempty, syms0)] -- NOTE ulterior necessity of logging statements: expansions of writes are progressive, so we may blitz through tagging all the writes, but reads could unravel one layer at a time
  -- takeWhile (not . null . rs_writes) $ foldl (\l _ -> l ++ [iterant $ head l]) [syms0] [0..] -- interesting that this doesn't seem to be possible
  
{-
in if sa_loc sa `elem` map fst reads && sa_loc sa' `elem` map snd reads
  then ([], nf_sas { rs_stmts = mempty }) -- already read: discard statements
  else ([(sa_loc sa, sa_loc sa')], nf_sas)
-}

expand_reads :: [Write] -> [SymApp] -> [SymApp]
expand_reads ws = mconcat . map (\sa ->
  let next_read_syms
        | arg0:rest <- sa_args sa = mconcat $ map (\sa' ->
            case sa_sym sa' of
              Sym (L _ (HsVar _ (L _ v')))
                | varString v' `elem` [
                    "newMVar", -- DEBUG
                    "newEmptyMVar",
                    "newTVar",
                    "newTVarIO",
                    "newIORef",
                    "newSTRef"
                  ] -> unref ws (sa' { sa_args = rest })
                | otherwise -> [sa']
          ) arg0
        | otherwise = [sa]
    in case sa_sym sa of
      Sym (L _ (HsVar _ (L _ v))) ->
        if | varString v `elem` [
              "readIORef",
              "readMVar",
              "takeMVar",
              "readTVar",
              "readTVarIO",
              "readSTRef",
              
              "atomicSwapIORef"
            ]
           -> next_read_syms
           
           | varString v == "atomicModifyIORefLazy_"
           -> map (\sa -> sa {
              sa_sym = TupleConstr (getSymLoc $ sa_sym sa),
              sa_args = [[sa], [sa]]
            }) next_read_syms
           
           | otherwise -> [sa]
      _ -> [sa]
  )
