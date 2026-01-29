{-# LANGUAGE BangPatterns, MagicHash, ScopedTypeVariables #-}
module Spec where

import Control.Exception
import System.IO.Unsafe

tryMaybe :: IO a -> IO (Maybe a)
tryMaybe a = catch (a >>= \ v -> return (Just v)) (\(e :: SomeException) -> return Nothing)

e :: ()
e = error "e"

run :: () -> Maybe ()
run _ = unsafePerformIO (tryMaybe (let !y = e in return y))
