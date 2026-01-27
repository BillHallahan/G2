{-# LANGUAGE ScopedTypeVariables #-}

module Catch1 where

import Control.Exception
import System.IO.Unsafe

f :: Int -> Int
f x = unsafePerformIO $ do
    catch (error "error") (\(_ :: SomeException) -> return x)

g :: Int -> Int
g x = unsafePerformIO $ do
    catch (case x >= 0 of
                True -> return 5
                False -> error "Negative")
          (\(_ :: SomeException) -> return x)
