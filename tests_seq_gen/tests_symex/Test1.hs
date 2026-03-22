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

smt_mixUp :: ([] a) -> ([] a)
smt_mixUp z1 = let !x = (let !y1 = strAt# z1 0#
                             !y2 = strAppend#  y1 z1
                             !y3 = strLt# z1 y2
                             !y4 = strLen# y1
                             !y7 = strLen# z1
                             !y8 = (+#) -1# y7
                             !y9 = strAt# z1 y8
                             !y10 = y9
                             !y11 = (if y3 then 1 else 2) in y9) in x

mixUp :: String -> String
mixUp [] = []
mixUp [x] = [x]
mixUp (x:xs@(_:_)) = init xs ++ [x] ++ [last xs]

comp :: String -> String
comp z1 = 
    let val = mixUp z1 in
    assert ((==) (tryMaybeUnsafe (smt_mixUp z1)) (tryMaybeUnsafe val)) val
