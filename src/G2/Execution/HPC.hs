{-# Language FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, StandaloneDeriving #-}

-- | Provides infrastructure to track which HPC ticks have been encountered during symbolic execution.
module G2.Execution.HPC ( HpcT
                        , HpcM
                        , HpcTracker
                        , LengthNTrack
                        
                        , hpcTracker
                        , immedHpcReducer
                        , onAcceptHpcReducer
                        
                        , lnt
                        , lengthNSubpathOrderer) where

import G2.Execution.Reducer
import G2.Language

import Control.Exception
import Control.Monad.Identity
import Control.Monad.IO.Class
import qualified Control.Monad.State.Lazy as SM
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import Data.List.Extra
import Data.Maybe
import Data.Monoid
import qualified Data.Text as T
import System.IO
import System.Clock

newtype HpcT m a = HpcT (SM.StateT (HS.HashSet (Int, T.Text)) m a) deriving (Functor, Applicative, Monad)

deriving instance Monad m => (SM.MonadState (HS.HashSet (Int, T.Text)) (HpcT m))

type HpcM a = HpcT Identity a

data HpcTracker = HPC {
                        hpc_ticks :: HM.HashMap (Int, T.Text) TimeSpec -- ^ The HPC ticks that execution has reached mapped to the time each was reached

                      , tick_count :: Int -- ^ Total number of HPC ticks that we could reach
                      , num_reached :: Int -- ^ Total number of HPC ticks currently reached by execution

                      , initial_time :: TimeSpec -- ^ The initial creation time of the HpcTracker
                      
                      , h_print_times :: Bool -- ^ Print the time each tick is reached?
                      , h_print_ticks :: Bool -- ^ Print each HPC tick number that was reached?
                      }

-- | State used by `hpcReducer`.
hpcTracker :: MonadIO m => State t
                        -> HS.HashSet (Maybe T.Text)
                        -> Bool -- ^ Print the time each tick is reached?
                        -> Bool -- ^ Print each HPC tick number that was reached?
                        -> m HpcTracker
hpcTracker s m pr_tms pr_ticks = do
    ts <- liftIO $ getTime Monotonic
    return $ HPC { hpc_ticks = HM.empty
                 , tick_count = HS.size $ HS.fromList $ evalASTs (getHPCTicks m) (expr_env s)
                 , num_reached = 0
                 , initial_time = ts
                 , h_print_times = pr_tms 
                 , h_print_ticks = pr_ticks }

unionHpcTracker :: HpcTracker -> HpcTracker -> HpcTracker
unionHpcTracker hpc1 hpc2 =
    let
        hpc_union = HM.unionWith min (hpc_ticks hpc1) (hpc_ticks hpc2)
    in
    HPC { hpc_ticks = hpc_union
        , tick_count = tick_count hpc1
        , num_reached = HM.size hpc_union
        , initial_time = initial_time hpc1
        , h_print_times = h_print_times hpc1
        , h_print_ticks = h_print_ticks hpc1 }

hpcInsert :: MonadIO m => Int -> T.Text -> HpcTracker -> m HpcTracker
hpcInsert i t hpc@(HPC { hpc_ticks = tr, num_reached = nr }) =
    case HM.member (i, t) tr of
        True -> return hpc
        False -> do
            ts <- liftIO $ getTime Monotonic
            return $ hpc { hpc_ticks = HM.insert (i, t) ts tr, num_reached = nr + 1 }

totalTickCount :: SM.MonadState HpcTracker m => m Int
totalTickCount = do
    (HPC { tick_count = ttc }) <- SM.get
    return ttc

-- | A reducer that tracks and prints the number of HPC ticks encountered during execution.
-- A HPC tick is considered reached as soon as a State reaches it.
immedHpcReducer :: (MonadIO m, SM.MonadState HpcTracker m) =>
                   HS.HashSet (Maybe T.Text) -- ^ A module to track tick count in
                -> Reducer m () r t
immedHpcReducer md = (mkSimpleReducer (const ()) logTick) { afterRed = after }
    where
        logTick _ _ s@(State {curr_expr = CurrExpr _ (Tick (HpcTick i tm) _)}) b
            | Just tm `HS.member` md = do
                hpc <- SM.get
                hpc'@(HPC { num_reached = nr }) <- hpcInsert i tm hpc
                SM.put hpc'
                hpc_tick_num <- totalTickCount
                liftIO $ putStr ("\r" ++ show nr ++ " / " ++ show hpc_tick_num)
                liftIO $ hFlush stdout
                return (NoProgress, [(s, ())], b)
        logTick _ _ s b = return (NoProgress, [(s, ())], b)

        after = afterHPC

-- | A reducer that tracks and prints the number of HPC ticks encountered during execution.
-- A HPC tick is considered reached only once a State that reached it is accepted.
onAcceptHpcReducer :: (MonadIO m, SM.MonadState HpcTracker m) =>
                      State t
                   -> HS.HashSet (Maybe T.Text) -- ^ Modules to track tick count in
                   -> IO (Reducer m HpcTracker r t)
onAcceptHpcReducer st md = do
    trck <- hpcTracker st md False False
    return (mkSimpleReducer (const trck) logTick) { onAccept = onAcc, afterRed = after }
    where
        logTick hpc _ s@(State {curr_expr = CurrExpr _ (Tick (HpcTick i tm) _)}) b
            | Just tm `HS.member` md = do
                hpc' <- hpcInsert i tm hpc
                return (NoProgress, [(s, hpc')], b)
        logTick rv _ s b = return (NoProgress, [(s, rv)], b)

        onAcc s b s_hpc = do
            ts <- liftIO $ getTime Monotonic
            let s_hpc' = s_hpc { hpc_ticks = HM.map (const ts) $ hpc_ticks s_hpc }
            SM.modify (`unionHpcTracker` s_hpc')
            (HPC { num_reached = nr }) <- SM.get
            hpc_tick_num <- totalTickCount
            liftIO $ putStr ("\r" ++ show nr ++ " / " ++ show hpc_tick_num)
            liftIO $ hFlush stdout
            return (s, b)

        after = afterHPC

afterHPC :: (MonadIO m, SM.MonadState HpcTracker m) => m ()
afterHPC = do
    hpc <- SM.get
    let init_ts = initial_time hpc
        ts = sort $ HM.elems (hpc_ticks hpc)
    assert (num_reached hpc == HM.size (hpc_ticks hpc))
        (liftIO $ putStrLn $ "\nTicks reached: " ++ show (num_reached hpc))
    liftIO $ putStrLn $ "Tick num: " ++ show (tick_count hpc)

    case ts of
        [] -> liftIO $ putStrLn $ "Last tick reached: N/A"
        (_:_) -> liftIO $ putStrLn $ "Last tick reached: " ++ showTS (last ts - init_ts)
    case h_print_ticks hpc of
        False -> return ()
        True -> liftIO $ do
            putStrLn "All ticks:"
            print . sort $ HM.keys (hpc_ticks hpc)
    case h_print_times hpc of
        False -> return ()
        True -> liftIO $ do
            putStrLn "All tick times:"
            mapM_ (\t -> putStrLn $ showTS (t - init_ts)) ts
            putStrLn "End of tick times"

showTS :: TimeSpec -> String
showTS (TimeSpec { sec = s, nsec = n }) = let str_n = show n in show s ++ "." ++ replicate (9 - length str_n) '0' ++ show n

getHPCTicks :: HS.HashSet (Maybe T.Text) -> Expr -> [(Int, T.Text)]
getHPCTicks m (Tick (HpcTick i m2) _) | Just m2 `HS.member` m = [(i, m2)]
getHPCTicks _ _ = []


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
                      -> Orderer m [(Int, T.Text)] Int r t
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