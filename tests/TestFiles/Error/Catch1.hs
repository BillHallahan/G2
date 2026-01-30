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

patOrCall1 :: Maybe Int -> Int
patOrCall1 x = unsafePerformIO $ do
    catch (h x) (\(_ :: PatternMatchFail) -> return 5)
    where
        h (Just y) | y >= 0 = return y
                   | otherwise = error "Negative"

patOrCall2 :: Maybe Int -> Int
patOrCall2 x = unsafePerformIO $ do
    catch (catch (h x) (\(_ :: PatternMatchFail) -> return 5)) (\(_ :: ErrorCall) -> return 50)
    where
        h (Just y) | y >= 0 = return y
                   | otherwise = error "Negative"