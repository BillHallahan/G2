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

smt_f1 :: ([] Char) -> ([] Char) -> ([] Char) -> ([] Char)
smt_f1 !z1 !z2 !z3 = let !x = (let !y1 = strAppend#  z1 z2 in y1) in x

placeholder :: ([] Char) -> ([] Char) -> ([] Char) -> ([] Char)
placeholder xs ys zs = xs ++ ys ++ zs

placeholderRet :: ([] Char) -> ([] Char) -> ([] Char) -> ([] Char)
placeholderRet xs ys zs = xs ++ ys ++ zs

comp z1 z2 z3 = 
    let val = placeholder z1 z2 z3; cond = (==) (tryMaybeUnsafe (smt_f1 z1 z2 z3)) (tryMaybeUnsafe val) in
 case cond of True -> val; False -> assert False (placeholderRet z1 z2 z3)
