{-# LANGUAGE LambdaCase #-}

module G2.Liquid.Inference.InfStack ( InfStack
                                    , runInfStack
                                    , execInfStack
                                    
                                    , infLiftIO

                                    , incrMaxDepthI
                                    , incrMaxCExI
                                    , incrMaxTimeI
                                    , incrMaxSynthSizeI

                                    , extraMaxDepthI
                                    , extraMaxCExI
                                    , extraMaxTimeI
                                    , maxSynthSizeI

                                    , logEventStartM
                                    , logEventEndM
                                    , getLogM

                                    , startLevelTimer
                                    , endLevelTimer

                                    , withConfigs

                                    , Event (..)
                                    , mapEvent

                                    , Counters (..)
                                    , incrLoopCountLog
                                    , incrSearchBelowLog
                                    , incrNegatedModelLog ) where

import G2.Data.Timer
import G2.Language
import G2.Liquid.Inference.Config

import Control.Monad.Reader
import Control.Monad.State.Lazy as S

import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T
import System.CPUTime
import Data.Time.Clock

data Event n = CExSE
             | InfSE n
             | Verify
             | Synth
             | UpdateMeasures
             | UpdateEvals
             deriving (Eq, Read, Show)

mapEvent :: (a -> b) ->  Event a -> Event b
mapEvent _ CExSE = CExSE
mapEvent f (InfSE n) = InfSE (f n)
mapEvent _ Verify = Verify
mapEvent _ Synth = Synth
mapEvent _ UpdateMeasures = UpdateMeasures
mapEvent _ UpdateEvals = UpdateEvals

data Counters = Counters { loop_count :: HM.HashMap (HS.HashSet Name) Int
                         , searched_below :: Int
                         , negated_models :: Int }

type InfStack m =  StateT (Timer (Event Name))
                    (StateT (Timer (HS.HashSet Name))
                        (StateT Counters (ReaderT Configs (StateT Progress m)))
                    )

runInfStack :: MonadIO m => Configs -> Progress -> InfStack m a
            -> m (a, Timer (Event Name), Timer (HS.HashSet Name), Counters)
runInfStack configs prog m = do
    ev_timer <- liftIO $ newTimer
    lvl_timer <- liftIO $ newTimer
    (((a, ev_tm), lvl_tm), loops) <- runProgresser 
                            (runConfigs 
                              (runStateT 
                                (runTimer (runTimer m ev_timer) lvl_timer) 
                                newCounter
                              ) configs
                            ) prog
    return (a, ev_tm, lvl_tm, loops)

execInfStack :: MonadIO m => Configs -> Progress -> InfStack m a -> m a
execInfStack configs prog s = return . (\(x, _, _, _) -> x) =<< runInfStack configs prog s 

infLiftIO :: MonadIO m => IO a -> InfStack m a
infLiftIO = lift . lift . lift . liftIO

incrMaxDepthI :: Monad m => InfStack m ()
incrMaxDepthI = lift . lift . lift $ incrMaxDepthM

incrMaxCExI :: Monad m => (T.Text, Maybe T.Text) -> InfStack m ()
incrMaxCExI = lift . lift . lift . incrMaxCExM

incrMaxTimeI :: Monad m => (T.Text, Maybe T.Text) -> InfStack m ()
incrMaxTimeI = lift . lift . lift . incrMaxTimeM

extraMaxCExI :: Monad m => (T.Text, Maybe T.Text) -> InfStack m Int
extraMaxCExI n = lift . lift . lift $ gets (extraMaxCEx n)

extraMaxDepthI :: Monad m => InfStack m Int
extraMaxDepthI = lift . lift . lift $ gets extraMaxDepth

extraMaxTimeI :: Monad m => (T.Text, Maybe T.Text) -> InfStack m NominalDiffTime
extraMaxTimeI n = lift . lift . lift $ gets (extraMaxTime n)

maxSynthSizeI :: Monad m => InfStack m MaxSize
maxSynthSizeI = lift . lift . lift $ maxSynthSizeM

incrMaxSynthSizeI :: Monad m => InfStack m ()
incrMaxSynthSizeI = lift . lift . lift $ incrMaxSynthSizeM

startLevelTimer :: MonadIO m => [Name] -> InfStack m () 
startLevelTimer = lift . logEventStartM . HS.fromList

endLevelTimer :: MonadIO m => InfStack m ()
endLevelTimer = lift $ logEventEndM

-- Configurations

withConfigs :: Monad m =>
               (Configs -> Configs)
            -> InfStack m a
            -> InfStack m a
withConfigs f m = do
    mapStateT (mapStateT (mapStateT (withReaderT f))) m

getConfigs :: InfConfigM m => m Configs
getConfigs = do
  g2_c <- g2ConfigM
  lh_c <- lhConfigM
  inf_c <- infConfigM
  return $ Configs { g2_config = g2_c
                   , lh_config = lh_c
                   , inf_config = inf_c }

-- Counters
newCounter :: Counters
newCounter = Counters { loop_count = HM.empty, searched_below = 0, negated_models = 0 }

incrLoopCountLog :: Monad m => [Name] -> InfStack m ()
incrLoopCountLog ns =
    let
        hs_ns = HS.fromList ns
    in
    lift . lift $ S.modify (\c@(Counters { loop_count = lcs }) ->
                          c { loop_count = HM.alter (\case (Just i) -> Just (i + 1)
                                                           Nothing -> Just 0) hs_ns lcs
                            }
                    )

incrSearchBelowLog :: Monad m => InfStack m ()
incrSearchBelowLog =
    lift . lift $ S.modify (\c@(Counters { searched_below = i }) -> c { searched_below = i + 1 })

incrNegatedModelLog :: Monad m => InfStack m ()
incrNegatedModelLog =
    lift . lift $ S.modify (\c@(Counters { negated_models = i }) -> c { negated_models = i + 1 })

