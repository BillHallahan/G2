module Spec where
import Control.Monad.Trans

{-# SPECIALIZE f :: IO Integer#-}
f :: MonadIO m => m Integer
f = liftIO (return 0)
