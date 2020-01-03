{-# LANGUAGE MultiWayIf, LambdaCase, NamedFieldPuns, TupleSections, DeriveDataTypeable, Rank2Types #-}

module Ra.Impure (
  reduce,
  expand_reads
) where

import GHC

import Data.Maybe ( catMaybes, fromMaybe, fromJust )
import Data.Generics ( Data, Typeable, mkQ )
import Data.Generics.Extra ( everywhereWithContextBut, everywhereWithContextLazyBut, extQT, gmapQT, GenericQT )
import Control.Arrow ( (&&&), (***), first, second )

import Ra ( reduce_deep, pat_match, and_pat_match_many )
import Ra.Lang
import Ra.Extra
import Ra.GHC.Util ( varString )

mk_write :: SymApp Sym -> Maybe Write
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


refresh_frames :: Writes -> SymApp Sym -> (PatMatchSyms, SymApp Sym)
refresh_frames ws sa =
  let (next_pms, next_stack) =
        first mconcat $ unzip $ map (\frame ->
            case frame of
              AppFrame { af_syms } ->
                (mempty,
                    if not $ null $ stbl_binds af_syms
                      then frame {
                          af_syms = af_syms {
                            stbl_table = fromJust $ and_pat_match_many $ stbl_binds af_syms -- fromJust <= changes can't regress on these binds: only make it more likely to bind. If this AppFrame exists, it must have succeeded the first time at least
                          }
                        }
                      else frame
                  )
              BindFrame { bf_syms } ->
                -- Note: forces argument ws a bit awkwardly; needs its own handler
                -- outside of generic query because otherwise it'll cause infinite
                -- recursion, and `extQT` was even more awkward
                
                let next_binds = snd (sa, map (second (concatMap (uncurry list_alt) . uncurry zip . (map (expand_reads ws) &&& map pure))) (stbl_binds bf_syms)) -- DEBUG
                    next_pms = pat_match next_binds
                in (next_pms, BindFrame (pms_syms next_pms))
              _ -> (mempty, frame)
          ) (sa_stack sa) -- DEBUG
  in (next_pms, sa { sa_stack = next_stack })

unref :: Writes -> SymApp Sym -> [SymApp Sym]
unref ws sa =
  let bases = snd $ foldl (\(max_len, sas) (pipes, next_sas) ->
          let m_next_max_len = foldr (\pipe ->
                  if is_parent (sa_loc sa) (sa_loc pipe)
                    then Just . max (length $ stack_apps $ sa_loc pipe) . fromMaybe 0
                    else id
                ) Nothing pipes
              m_ret = fmap (\sa' -> (\case -- encode shadowing rule: deepest matching stack loc wins
                  GT -> (,sas)
                  EQ -> (,sas <> next_sas)
                  LT -> (,next_sas)
                ) $ compare max_len sa') -- DEBUG
                (snd ((sa, pipes), m_next_max_len)) -- DEBUG
                <*> fmap (max max_len) m_next_max_len
          in if | elem (getSymLoc $ sa_sym sa) $ map (getSymLoc . sa_sym) pipes
                , Just ret <- m_ret -> ret -- by only taking `w_sym`, encode the law that write threads are not generally the threads that read (obvious saying it out loud, but it does _look_ like we're losing information here)
                | otherwise -> (max_len, sas)
        ) (0, mempty) ws
  
  in map (\sa' -> sa' {
      sa_args = sa_args sa' <> sa_args sa,
      sa_stack = sa_stack sa' <> sa_stack sa -- NOTE another instance of substitution law: merge stacks
    }) bases


permute2 = concatMap (\(pipes, syms) -> [(pipe, sym) | pipe <- pipes, sym <- syms]) -- TODO stopgap before implementing Map

reduce :: [SymApp Sym] -> ReduceSyms
reduce sas0 =
  let syms0 = mconcat $ map reduce_deep sas0
  
      f0 = (mempty,)
      
      go :: [Write] -> GenericQT (Bool, [DoStmt])
      go writes = first ((or *** mconcat) . unzip) . (
          gmapQT (go writes)
          `extQT` ( -- TODO there's some canonical way to do this non-imperatively. even with Bool not sharing classes with []. find it.
              ( -- ehh.
                  first pure -- eh.
                  . first (second (uncurry (<>)) . fpackl packr) . fpackr packl . second ((rs_stmts &&& rs_syms) . mconcat . map reduce_deep)
                  . fpackr packl . first (uncurry (||)) . fpackr packl -- ((Bool, [DoStmt]), [SymApp Sym])
                  . second (
                      fpackl packr . first ((or *** mconcat) . unzip . concat)  -- (Bool, ([DoStmt], [SymApp Sym]))
                      . unzip
                      . map (gmapQT (go writes)) -- [([(Bool, [DoStmt])], SymApp Sym)]
                    )
                  . (or *** concatMap (uncurry list_alt) . uncurry zip) -- (Bool, [SymApp Sym])
                  . fpackl packr -- ([Bool], ([[SymApp Sym]], [[SymApp Sym]]))
                  . (unzip . map ((not . null &&& id) . expand_reads writes) &&& map pure) -- (([Bool], [[SymApp Sym]]), [[SymApp Sym]])
                )
            )
          `extQT` ((\fr -> case fr of { BindFrame {} -> f0 fr; _ -> gmapQT (go writes) fr }) :: StackFrame -> ([(Bool, [DoStmt])], StackFrame))
        )
      
      iterant :: [DoStmt] -> [DoStmt] -> (Writes, ([DoStmt], [DoStmt])) -- always act on syms0, return what we get on this phase
      iterant old_stmts new_stmts =
        let (old_writes, new_writes) = both (catMaybes . map mk_write) (old_stmts, new_stmts)
            ((old_changed, new_stmts_from_old), (next_old_stmts, next_syms)) = go new_writes (old_stmts, rs_syms syms0)
            ((new_changed, new_stmts_from_new), next_new_stmts) = go (old_writes <> new_writes) new_stmts

        in (
            old_writes <> new_writes,
            (
                old_stmts <> new_stmts,
                new_stmts_from_old <> (if old_changed then next_old_stmts else mempty)
                <> new_stmts_from_new <> (if new_changed then next_new_stmts else mempty)
              )
          )
        
  in (\(ws, (old_stmts, new_stmts)) -> ReduceSyms (snd $ go ws (rs_syms syms0)) (old_stmts <> new_stmts))
    $ head
    $ head
    $ filter ((\(last_writes, (_, new_stmts)) ->
        let next_writes_map = permute2 $ catMaybes $ map mk_write new_stmts
            last_writes_map = permute2 last_writes
        in snd ((next_writes_map, last_writes_map), all (\next -> any (\prev -> 
              uncurry (&&) $ (uncurry (&&) . both (uncurry stack_eq) . (both fst &&& both snd) *** uncurry (==)) $ (both (both sa_loc) &&& both (both sa_sym)) (next, prev) -- eh.
            ) last_writes_map) next_writes_map)
          -- sometimes pointfree isn't worth it: ((uncurry (&&)).) . uncurry (***) . both ((uncurry (&&).) . (curry (uncurry stack_eq . both sa_loc) &&& curry (uncurry (==) . both sa_sym)))
      ) . head)
    $ iterate (\l -> (uncurry iterant $ snd $ head l):l) [(mempty, (mempty, rs_stmts syms0))] -- NOTE ulterior necessity of logging statements: expansions of writes are progressive, so we may blitz through tagging all the writes, but reads could unravel one layer at a time
  -- takeWhile (not . null . rs_writes) $ foldl (\l _ -> l ++ [iterant $ head l]) [syms0] [0..] -- interesting that this doesn't seem to be possible
  
{-
in if sa_loc sa `elem` map fst reads && sa_loc sa' `elem` map snd reads
  then ([], nf_sas { rs_stmts = mempty }) -- already read: discard statements
  else ([(sa_loc sa, sa_loc sa')], nf_sas)
-}

expand_reads :: [Write] -> SymApp Sym -> [SymApp Sym]
expand_reads = expand_reads' 0 where
  expand_reads' n ws sa
    | n < sum (map (length . fst) ws) = -- reeeeeeeally crude upper bound for now
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
                      ] -> concatMap (uncurry list_alt) $ map ((expand_reads' (n + 1) ws) &&& pure) $ unref ws (sa' { sa_args = rest })
                    | otherwise -> []
              ) arg0
            | otherwise = []
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
             -> snd (sa, next_read_syms) -- DEBUG
             
             | varString v == "atomicModifyIORefLazy_"
             -> map (\sa -> sa {
                sa_sym = TupleConstr (getSymLoc $ sa_sym sa),
                sa_args = [[sa], [sa]]
              }) next_read_syms
             
             | otherwise -> []
        _ -> []
    | otherwise = []
