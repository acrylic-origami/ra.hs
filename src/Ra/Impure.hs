{-# LANGUAGE MultiWayIf, LambdaCase, NamedFieldPuns #-}

module Ra.Impure (
  reduce,
  expand_reads
) where

import GHC

import Data.Maybe ( catMaybes )
import Control.Arrow ( (&&&), (***), first, second )

import Ra ( reduce_deep, pat_match )
import Ra.Lang
import Ra.Extra
import Ra.GHC.Util ( varString )

mk_writes sa
  | Sym (L _ (HsVar _ (L _ v))) <- sa_sym sa =
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
       -- TODO URGENT this may cause an infinite loop as is
       
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

reduce :: ReduceSyms -> ReduceSyms
reduce syms0 =
  let iterant :: [DoStmt] -> ReduceSyms
      iterant stmts =
        let writes = catMaybes $ map mk_writes stmts
            update_stack sa =
              let (next_pms', next_stack) = (mconcat *** SB) $ unzip $ map (\case
                      af@(AppFrame { af_syms }) ->
                        let (next_rs', next_binds) = (first mconcat) $ unzip $ map ((snd &&& second rs_syms) . second (mconcat . map (expand_reads writes))) (stbl_binds af_syms)
                            next_pms'' = pat_match next_binds
                        in (next_pms'' {
                            pms_stmts = pms_stmts next_pms'' <> rs_stmts next_rs'
                          }, af {
                            af_syms = pms_syms next_pms''
                          })
                      v -> (mempty, v)
                    ) (unSB $ sa_stack sa)
                  (next_args_pms, next_args) = unzip $ map (unzip . map update_stack) (sa_args sa)
              in (next_pms' <> (mconcat $ mconcat next_args_pms), sa {
                sa_stack = next_stack,
                sa_args = next_args
              })
              
            (next_pms, next_rs) = (mconcat *** mconcat) $ unzip $ map (second (expand_reads writes) . update_stack) $ rs_syms syms0
        in next_rs {
          rs_stmts = (rs_stmts next_rs) <> (pms_stmts next_pms)
        }
      stmtsn = concat $ until (null . head) (\l -> (rs_stmts $ iterant $ head l) : l) [rs_stmts syms0] -- NOTE ulterior necessity of logging statements: expansions of writes are progressive, so we may blitz through tagging all the writes, but reads could unravel one layer at a time
  in iterant stmtsn
  -- takeWhile (not . null . rs_writes) $ foldl (\l _ -> l ++ [iterant $ head l]) [syms0] [0..] -- interesting that this doesn't seem to be possible

unref :: Writes -> SymApp -> [SymApp]
unref ws sa =
  let bases = concatMap snd
        $ filter (
            uncurry (&&)
            . (
                 -- beware of unLoc and conflicts between variables
                elem (getSymLoc $ sa_sym sa) . map (getSymLoc . sa_sym)
                &&& (elem (sa_loc sa)) . map sa_loc
              ) . fst
          ) ws -- by only taking `w_sym`, encode the law that write threads are not generally the threads that read (obvious saying it out loud, but it does _look_ like we're losing information here)
  in map (\sa' -> sa' {
      sa_args = sa_args sa' <> sa_args sa,
      sa_stack = mapSB (<>(unSB $ sa_stack sa)) (sa_stack sa') -- NOTE another instance of substitution law: merge stacks
    }) bases

expand_reads :: Writes -> SymApp -> ReduceSyms
expand_reads ws sa =
  let m_next_args :: [ReduceSyms]
      m_next_args = map (mconcat . map (\sa' ->
          lift_rs_syms2 list_alt (expand_reads ws sa') (mempty { rs_syms = [sa'] })
        )) (sa_args sa)
      next_argd_sym = mempty { rs_syms = [sa {
         sa_args = map rs_syms m_next_args
       }] }
       
      expanded :: [SymApp]
      expanded = case sa_sym sa of
        Sym (L _ (HsVar _ (L _ v))) ->
          if | varString v == "newEmptyMVar" -> unref ws sa
             | varString v `elem` [
                "newMVar", -- DEBUG
                "newTVar",
                "newTVarIO",
                "newIORef",
                "newSTRef"
              ] -> unref ws (sa {
                sa_args = tail (sa_args sa)
              })
              
             | varString v == "atomicSwapIORef"
             , vars:_:rest <- sa_args sa
             -> map (\sa' -> sa' {
                sa_args = sa_args sa' <> rest
              }) vars
             
             -- `atomicModifyIORef2Lazy` is the responsibility of the write coordinator, which will unpackage the funapp and flow it down here eventually
             
             -- | varString v == "tryTakeMVar"
             -- -> 
             -- | varString v == "bindSTM"
             -- , vars:fns:rest <- sa_args sa
             -- -> map (\sa' -> sa' {
             --    sa_args = vars:rest
             --  }) fns
          
             | otherwise -> mempty
        _ -> mempty
  in (((mconcat m_next_args) { rs_syms = mempty })<>) 
    $ mconcat $ map reduce_deep 
    $ rs_syms $ lift_rs_syms2 list_alt (mconcat $ map reduce_deep expanded) next_argd_sym -- a bunch of null handling that looks like a mess because it is
  -- STACK good: relies on the pipe stack being correct