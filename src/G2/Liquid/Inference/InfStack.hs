module G2.Liquid.Inference.InfStack ( InfStack
                                    , runInfStack
                                    , execInfStack
                                    
                                    , infLiftIO

                                    , logEventStartM
                                    , logEventEndM
                                    , getLogM

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

import qualified Data.Text as T
import System.CPUTime

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

data Counters = Counters { loop_count :: Int
                         , searched_below :: Int
                         , negated_models :: Int }

type InfStack m =  StateT (Timer (Event Name)) (StateT Counters (ReaderT Configs (StateT Progress m)))

runInfStack :: MonadIO m => Configs -> Progress -> InfStack m a -> m (a, Timer (Event Name), Counters)
runInfStack configs prog m = do
    timer <- liftIO $ newTimer
    ((a, tm), loops) <- runProgresser (runConfigs (runStateT (runTimer m timer) newCounter) configs)prog
    return (a, tm, loops)

execInfStack :: MonadIO m => Configs -> Progress -> InfStack m a -> m a
execInfStack configs prog s = return . (\(x, _, _) -> x) =<< runInfStack configs prog s 

infLiftIO :: MonadIO m => IO a -> InfStack m a
infLiftIO = lift . lift . liftIO

-- Configurations

withConfigs :: Monad m =>
               (Configs -> Configs)
            -> InfStack m a
            -> InfStack m a
withConfigs f m = do
    mapStateT (mapStateT (withReaderT f)) m

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
newCounter = Counters { loop_count = 0, searched_below = 0, negated_models = 0 }

incrLoopCountLog :: Monad m => InfStack m ()
incrLoopCountLog =
    lift $ S.modify (\c@(Counters { loop_count = i }) -> c { loop_count = i + 1 })

incrSearchBelowLog :: Monad m => InfStack m ()
incrSearchBelowLog =
    lift $ S.modify (\c@(Counters { searched_below = i }) -> c { searched_below = i + 1 })

incrNegatedModelLog :: Monad m => InfStack m ()
incrNegatedModelLog =
    lift $ S.modify (\c@(Counters { negated_models = i }) -> c { negated_models = i + 1 })

