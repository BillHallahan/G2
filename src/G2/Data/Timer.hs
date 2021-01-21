{-# LANGUAGE FlexibleInstances #-}

module G2.Data.Timer ( Timer
                     , TimerLog
                     , newTimer
                     , logEventStart
                     , logEventEnd
                     , getLog

                     , runTimer
                     , logEventStartM
                     , logEventEndM
                     , getLogM

                     , sumLog
                     , logToSecs ) where

import Control.Monad.IO.Class 
import Control.Monad.Reader
import Control.Monad.State.Lazy
import Data.List
import qualified Data.Text as T
import System.CPUTime

type TimerLog label = [(label, Integer)]

data Timer label =
    Timer { timer_log :: TimerLog label -- ^ Labelled events with time measurements (in picoseconds)
          , for_next :: Maybe (label, Integer) -- ^ What is the next label, and when did we start timing?
          }

newTimer :: IO (Timer label)
newTimer = do
    return $ Timer { timer_log = []
                   , for_next = Nothing } 

logEventStart :: label -> Timer label -> IO (Timer label)
logEventStart label timer = do
    curr <- getCPUTime
    return $ logEventStart' label curr timer

logEventStart' :: label -> Integer -> Timer label -> Timer label
logEventStart' label curr timer =
    timer { for_next = Just (label, curr) } 

logEventEnd :: Timer label -> IO (Timer label)
logEventEnd timer = do
    curr <- getCPUTime
    return $ logEventEnd' curr timer

logEventEnd' :: Integer -> Timer label -> Timer label
logEventEnd' curr (Timer { timer_log = lg, for_next = Just (label, lst) }) =
    Timer { timer_log = (label, curr - lst):lg
          , for_next = Nothing }
logEventEnd' _ _ = error "Timer ended but never started"

getLog :: Timer label -> TimerLog label
getLog = timer_log

runTimer :: StateT (Timer label) m a -> Timer label -> m (a, Timer label)
runTimer = runStateT

logEventStartM :: MonadIO m => label -> StateT (Timer label) m ()
logEventStartM n = do
    curr <- liftIO $ getCPUTime
    modify' (logEventStart' n curr)

logEventEndM :: MonadIO m => StateT (Timer label) m ()
logEventEndM = do
    curr <- liftIO $ getCPUTime
    modify' (logEventEnd' curr)

getLogM :: Monad m => StateT (Timer label) m (TimerLog label)
getLogM = gets getLog

-- Working with the generated logs

sumLog :: Eq label => TimerLog label -> TimerLog label
sumLog tl =
    let
        labs = nub $ map fst tl
        grped = map (sum . map snd)
              $ map (\l -> filter (\(l', _) -> l == l') tl) labs
    in
    zip labs grped

logToSecs :: TimerLog label -> [(label, Double)]
logToSecs = map (\(l, s) -> (l, fromInteger s / (10 ^ 12)))
