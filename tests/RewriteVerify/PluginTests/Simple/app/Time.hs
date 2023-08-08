module Time where
import Control.Monad.Trans

{-# SPECIALIZE getCPUTime :: IO Integer#-}
getCPUTime :: MonadIO m => m Integer
getCPUTime = liftIO (return 0)
