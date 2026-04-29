{-# LANGUAGE BangPatterns, MagicHash, ScopedTypeVariables, ViewPatterns #-}
module Spec where
import GHC.Prim2
import GHC.Types2
import GHC.Stack
import Control.Exception
import Data.Functor.Classes
import System.IO.Unsafe


tryMaybe :: IO a -> IO (Maybe a)
tryMaybe a = catch (a >>= \v -> return (Just v)) (\(e :: SomeException) -> return Nothing)

tryMaybeUnsafe :: a -> Maybe a
tryMaybeUnsafe x = unsafePerformIO $ tryMaybe (let !y = x in return y)

smt_elem :: Int -> (([]) Int) -> Bool
smt_elem (I# z1) z2 = let !x = strLt# [] [] in x

placeholder :: Int -> (([]) Int) -> Bool
placeholder = elem

comp :: Int -> [Int] -> Bool
comp z1 z2 =
    let val = placeholder z1 z2; cond = (==) (tryMaybeUnsafe (smt_elem z1 z2)) (tryMaybeUnsafe val) in
 case cond of True -> assert False val; False -> assert False val
