module Risers (c_risers, ilSize, illSize, tFst, tSnd) where

import Prelude hiding (length)

data IntList = Int :+: IntList | ILEmp
infixr 5 :+:

data IntListList = IntList :++: IntListList | ILLEmp
infixr 5 :++:

{-@ measure ilSize @-}
ilSize :: IntList -> Int
ilSize ILEmp = 0
ilSize (x :+: xs) = 1 + ilSize xs

{-@ measure illSize @-}
illSize :: IntListList -> Int
illSize ILLEmp = 0
illSize (x :++: xs) = 1 + illSize xs


c_risers :: IntList -> IntListList
c_risers xs = risers (0 :+: xs)

risers           :: IntList -> IntListList
risers ILEmp       = ILLEmp
risers (x :+: ILEmp)       = (x :+: ILEmp) :++: ILLEmp
risers (x :+: y :+: etc)
  | x <= y       = ( x :+: s) :++: ss
  | otherwise    = (x :+: ILEmp ) :++: (s :++: ss)
    where
      T s ss    = safeSplit $ risers (y :+: etc)

data IL_ILL_T = T IntList IntListList

{-@ measure tFst @-}
tFst :: IL_ILL_T -> IntList
tFst (T x _) = x

{-@ measure tSnd @-}
tSnd :: IL_ILL_T -> IntList
tSnd (T x _) = x

safeSplit :: IntListList -> IL_ILL_T
safeSplit (x :++: xs) = T x xs
safeSplit _      = die "don't worry, be happy"

{-@ die :: {v:String | false} -> IL_ILL_T @-}
die :: String -> IL_ILL_T
die str = error ("Oops, I died!" ++ str)
