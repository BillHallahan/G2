
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

{-# NOINLINE strUnit# #-}
strUnit# x = [I# x]

smt_count :: Int -> (([]) Int) -> Int
smt_count (I# z1) z2 = let !x = (let 
                                    !y1 = strAt# z2 z1;
                                    !y2 = strLen# y1;
                                    !_let_1 = y2;
                                    !y3 = strLen# z2;
                                    !_let_2 = y3;
                                    !y4 = [I# z1];
                                    !_let_3 = y4;
                                    !y5 = strContains# z2 _let_3;
                                    !y6 = strReverse# z2;
                                    !y7 = strEq# z2 y6;
                                    !y8 = strUnit# 0#;
                                    !y9 = strEq# z2 y8;
                                    !y10 = strPrefixOf# _let_3 z2;
                                    !y11 = (if y10 then _let_2 else _let_1);
                                    !y12 = (if y9 then _let_2 else y11);
                                    !y13 = (if y7 then y12 else _let_1);
                                    !y14 = (if y5 then y13 else 0#) in y14) in I# x

placeholder :: Int -> (([]) Int) -> Int
placeholder = count

count :: Int -> [Int] -> Int
count x [] = 0
count x (y:ys) =
  case x == y of
    True -> 1 + (smt_count x ys)
    _ -> count x ys

placeholderRet :: Int -> (([]) Int) -> Int
placeholderRet = count

comp z1 z2 = 
    let val = placeholder z1 z2; cond = (==) (tryMaybeUnsafe (smt_count z1 z2)) (tryMaybeUnsafe val) in
 case cond of True -> val; False -> assert False (placeholderRet z1 z2)
