{-# Language FlexibleContexts, FlexibleInstances, GeneralisedNewtypeDeriving,
             MultiParamTypeClasses, StandaloneDeriving #-}

-- | Provides infrastructure to track which HPC ticks have been encountered during symbolic execution.
module G2.Execution.HPC ( HpcT
                        , HpcM
                        , HpcTracker
                        , LengthNTrack
                        
                        , hpcTracker
                        , hpcReducer
                        
                        , lnt
                        , lengthNSubpathOrderer) where

import G2.Execution.Reducer
import G2.Language

import Control.Monad.Identity
import Control.Monad.IO.Class
import qualified Control.Monad.State.Lazy as SM
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import Data.Maybe
import Data.Monoid
import qualified Data.Text as T
import System.IO

newtype HpcT m a = HpcT (SM.StateT (HS.HashSet (Int, T.Text)) m a) deriving (Functor, Applicative, Monad)

deriving instance Monad m => (SM.MonadState (HS.HashSet (Int, T.Text)) (HpcT m))

type HpcM a = HpcT Identity a

data HpcTracker = HPC
                    (HS.HashSet (Int, T.Text)) -- ^ The HPC ticks that execution has reached
                    (Maybe Int) -- ^ Total number of HPC ticks that we could reach.  See [HPC Total Tick Count]

-- [HPC Total Tick Count]
-- We want to know (as good an approximation as possible of) how many HPC ticks our execution
-- could potentially reach.  Knowing this requires the state, after memory cleaning has occurred.
--
-- Memory cleaning happens after the Reducer has been created, so we want to delay computing the
-- total tick count until execution has begun.  But we don't want to repeatedly recompute
-- the total tick count, because this requires scanning the entire state.  So instead,
-- we track the total tick count as a `Maybe Int`, which is `Nothing` (if we have not yet computed
-- the total tick count) or `Just i`, where `i` is the total tick count.

-- | State used by `hpcReducer`.
hpcTracker :: HpcTracker
hpcTracker = HPC HS.empty Nothing

hpcInsert :: Int -> T.Text -> HpcTracker -> HpcTracker
hpcInsert i t (HPC tr ttc) = HPC (HS.insert (i, t) tr) ttc

totalTickCount :: SM.MonadState HpcTracker m => Maybe T.Text -> State t -> m Int
totalTickCount m s = do
    HPC tr ttc <- SM.get
    case ttc of
        Just i -> return i
        Nothing -> do
            let i = getSum $ evalASTs (countHPCTicks m) (expr_env s)
            SM.put . HPC tr $ Just i
            return i

-- | A reducer that tracks and prints the number of HPC ticks encountered during execution.
hpcReducer :: (MonadIO m, SM.MonadState HpcTracker m) =>
              Maybe T.Text -- ^ A module to track tick count in
           -> Reducer m () t
hpcReducer md = mkSimpleReducer (const ()) logTick
    where
        logTick _ s@(State {curr_expr = CurrExpr _ (Tick (HpcTick i tm) _)}) b
            | Just tm == md = do
                SM.modify (hpcInsert i tm)
                HPC seen _ <- SM.get
                hpc_tick_num <- totalTickCount md s
                liftIO $ putStr ("\r" ++ show (HS.size seen) ++ " / " ++ show hpc_tick_num)
                liftIO $ hFlush stdout
                return (NoProgress, [(s, ())], b)
        logTick _ s b = return (NoProgress, [(s, ())], b)

countHPCTicks :: Maybe T.Text -> Expr -> Sum Int
countHPCTicks m (Tick (HpcTick _ m2) _) | m == Just m2 = Sum 1
countHPCTicks _ _ = 0


-------------------------------------------------------------------------------
-- Length N Subpaths
-------------------------------------------------------------------------------

newtype LengthNTrack = LNT { unLNT :: HM.HashMap [(Int, T.Text)] Int }

-- | State used by `lengthNSubpathOrderer`.
lnt :: LengthNTrack
lnt = LNT HM.empty

-- | Orders states based on length N subpaths.
-- Each time execution switches states, the state with the least common most
-- recently explored length N subpath is chosen.
--
-- Based on the paper:
--     Steering Symbolic Execution to Less Traveled Paths
--     You Li, Zhendong Su, Linzhang Wang, Xuandong Li
lengthNSubpathOrderer :: SM.MonadState LengthNTrack m =>
                         Int -- ^ N, the length of the subpaths to track
                      -> Orderer m [(Int, T.Text)] Int t
lengthNSubpathOrderer n = (mkSimpleOrderer initial order update) { stepOrderer  = step }
    where
        initial _ = []

        order p _ _ = do
            LNT sp <- SM.get
            return $ fromMaybe 0 (HM.lookup p sp)

        update p _ _ = p

        step p _ _ (State { curr_expr = CurrExpr _ (Tick (HpcTick i m) _) }) = do
            let p' = take n $ (i, m):p
            SM.modify (LNT . HM.insertWith (+) p' 1 . unLNT)
            return p'
        step p _ _ _ = return p