module G2.Liquid.Inference.InfStack ( InfStack
                                    , runInfStack
                                    , execInfStack
                                    
                                    , infLiftIO

                                    , logEventStartM
                                    , logEventEndM
                                    , getLogM

                                    , withConfigs

                                    , Event (..)
                                    , mapEvent ) where

import G2.Data.Timer
import G2.Language
import G2.Liquid.Inference.Config

import Control.Monad.Reader
import Control.Monad.State.Lazy

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

type InfStack m = StateT (Timer (Event Name)) (ReaderT Configs (StateT Progress m))

runInfStack :: MonadIO m => Configs -> Progress -> InfStack m a -> m (a, Timer (Event Name))
runInfStack configs prog m = do
    timer <- liftIO $ newTimer
    runProgresser (runConfigs (runTimer m timer) configs) prog

execInfStack :: MonadIO m => Configs -> Progress -> InfStack m a -> m a
execInfStack configs prog s = return . fst =<< runInfStack configs prog s 

infLiftIO :: MonadIO m => IO a -> InfStack m a
infLiftIO = lift . lift . liftIO

-- Configurations

withConfigs :: Monad m =>
               (Configs -> Configs)
            -> InfStack m a
            -> InfStack m a
withConfigs f m = do
    mapStateT (withReaderT f) m

getConfigs :: InfConfigM m => m Configs
getConfigs = do
  g2_c <- g2ConfigM
  lh_c <- lhConfigM
  inf_c <- infConfigM
  return $ Configs { g2_config = g2_c
                   , lh_config = lh_c
                   , inf_config = inf_c }
