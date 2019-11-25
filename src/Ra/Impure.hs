{-# LANGUAGE MultiWayIf, LambdaCase, NamedFieldPuns, TupleSections, DeriveDataTypeable #-}

module Ra.Impure (
  reduce,
  expand_reads
) where

import GHC

import Data.Maybe ( catMaybes, fromMaybe, fromJust )
import Data.Generics ( Data, Typeable, mkQ )
import Data.Generics.Extra ( everywhereWithContextBut, everywhereWithContextLazyBut, mkQT, extQT )
import Control.Arrow ( (&&&), (***), first, second )

import Ra ( reduce_deep, pat_match, and_pat_match_many )
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


refresh_frames :: Writes -> Stack -> (PatMatchSyms, Stack)
refresh_frames ws st = first mconcat $ unzip $ map (\frame ->
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
        
        let next_binds = map (second (expand_reads ws)) (stbl_binds bf_syms)
            next_pms = pat_match next_binds
        in (next_pms, BindFrame (pms_syms next_pms))
      _ -> (mempty, frame)
  ) st -- DEBUG

unref :: Writes -> SymApp -> [SymApp]
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


type WriteSite = (Stack, Stack) -- pipe and value locations

permute2 = concatMap (\(pipes, syms) -> [(pipe, sym) | pipe <- pipes, sym <- syms]) -- TODO stopgap before implementing Map

reduce :: ReduceSyms -> [ReduceSyms]
reduce syms0 =
  let iterant :: [DoStmt] -> (Writes, ReduceSyms) -- always act on syms0, return what we get on this phase
      iterant stmts =
        let writes = catMaybes $ map mk_write stmts
            f0 = (mempty,)
            (next_stmts, next_rs) = everywhereWithContextLazyBut
                (<>)
                (False `mkQ` (\case { BindFrame {} -> True; _ -> False } :: StackFrame -> Bool))
                (
                    f0
                    `mkQT` (\sas ->
                        (mconcat *** concat)
                        $ unzip
                        $ map (\sa ->
                            let (next_pms, next_stack) = refresh_frames writes $ sa_stack sa -- re-pat-match the bindings 
                                next_rs = reduce_deep $ sa { sa_stack = next_stack }
                            in (
                                pms_stmts next_pms <> rs_stmts next_rs,
                                rs_syms next_rs
                              )
                          )
                        $ expand_reads writes sas -- DEBUG
                      )
                  ) mempty syms0
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
