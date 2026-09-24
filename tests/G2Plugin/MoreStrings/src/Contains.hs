module Contains where

import G2.Plugin

{-# ANN matchPrefix (SMTEquivIs "matchPrefixSmt") #-}
matchPrefix :: String -> String -> Bool
matchPrefix [] _ = True
matchPrefix _ [] = False
matchPrefix (n:ns) (h:hs) = n == h && matchPrefix ns hs

matchPrefixSmt :: String -> String -> Bool
matchPrefixSmt = smtPrefixOf

{-# ANN contains' (SMTEquivIsWithConfig "containsSmt" "--smt cvc5") #-}
contains' :: String -> String -> Bool
contains' [] _ = True
contains' _ [] = False
contains' needle haystack@(_:t) = matchPrefix needle haystack || contains' needle t

containsSmt :: String -> String -> Bool
containsSmt needle haystack = smtContains haystack needle

{-# ANN myAppend (SMTEquivIs "myAppendSmt") #-}
myAppend :: String -> String -> String
myAppend [] ys = ys
myAppend (x:xs) ys = x : myAppend xs ys

myAppendSmt :: String -> String -> String
myAppendSmt xs ys = xs $++ ys

{-# ANN myReverse (SMTEquivIs "myReverseSmt") #-}
myReverse :: String -> String
myReverse [] = []
myReverse (x:xs) = myReverse xs ++ [x]

myReverseSmt :: String -> String
myReverseSmt = smtReverse

{-# ANN propContainsTransitive (PropWithConfig "--smt cvc5") #-}
propContainsTransitive :: String -> String -> String -> Bool
propContainsTransitive xs ys zs = contains' xs ys && contains' ys zs ==> contains' xs zs

{-# ANN propMatchPrefixRefl Prop #-}
propMatchPrefixRefl :: String -> Bool
propMatchPrefixRefl xs = matchPrefix xs xs == True

{-# ANN propMatchPrefixNil Prop #-}
propMatchPrefixNil :: String -> Bool
propMatchPrefixNil xs = matchPrefix [] xs == True

{-# ANN propMatchPrefixTransitive Prop #-}
propMatchPrefixTransitive :: String -> String -> String -> Bool
propMatchPrefixTransitive xs ys zs = matchPrefix xs ys && matchPrefix ys zs ==> matchPrefix xs zs

{-# ANN propMatchPrefixAppend Prop #-}
propMatchPrefixAppend :: String -> String -> Bool
propMatchPrefixAppend xs ys = matchPrefix xs (xs ++ ys) == True

{-# ANN propMatchPrefixCons Prop #-}
propMatchPrefixCons :: Char -> String -> String -> Bool
propMatchPrefixCons x xs ys = matchPrefix xs ys ==> matchPrefix (x:xs) (x:ys)

{-# ANN propMatchPrefixStep Prop #-}
propMatchPrefixStep :: Char -> String -> Char -> String -> Bool
propMatchPrefixStep n ns h hs = matchPrefix (n:ns) (h:hs) == (n == h && matchPrefix ns hs)

{-# ANN propMatchPrefixEmptyHaystack Prop #-}
propMatchPrefixEmptyHaystack :: Char -> String -> Bool
propMatchPrefixEmptyHaystack x xs = matchPrefix (x:xs) [] == False

{-# ANN propContainsRefl (PropWithConfig "--smt cvc5") #-}
propContainsRefl :: String -> Bool
propContainsRefl xs = contains' xs xs == True

{-# ANN propContainsNilNeedle (PropWithConfig "--smt cvc5") #-}
propContainsNilNeedle :: String -> Bool
propContainsNilNeedle xs = contains' [] xs == True

{-# ANN propContainsEmptyHaystack (PropWithConfig "--smt cvc5") #-}
propContainsEmptyHaystack :: Char -> String -> Bool
propContainsEmptyHaystack x xs = contains' (x:xs) [] == False

{-# ANN propPrefixImpliesContains (PropWithConfig "--smt cvc5") #-}
propPrefixImpliesContains :: String -> String -> Bool
propPrefixImpliesContains xs ys = matchPrefix xs ys ==> contains' xs ys

{-# ANN propContainsAppendLeft (PropWithConfig "--smt cvc5") #-}
propContainsAppendLeft :: String -> String -> Bool
propContainsAppendLeft xs ys = contains' xs (xs ++ ys) == True

{-# ANN propContainsAppendRight (PropWithConfig "--smt cvc5") #-}
propContainsAppendRight :: String -> String -> Bool
propContainsAppendRight xs ys = contains' ys (xs ++ ys) == True

{-# ANN propContainsMono (PropWithConfig "--smt cvc5") #-}
propContainsMono :: String -> String -> String -> Bool
propContainsMono xs ys zs = (contains' xs ys ==> contains' xs (ys ++ zs)) && (contains' xs zs ==> contains' xs (ys ++ zs))

{-# ANN propContainsCons (PropWithConfig "--smt cvc5") #-}
propContainsCons :: Char -> String -> String -> Bool
propContainsCons y xs ys = contains' xs ys ==> contains' xs (y:ys)

{-# ANN propContainsMiddle (PropWithConfig "--smt cvc5") #-}
propContainsMiddle :: String -> String -> String -> Bool
propContainsMiddle xs ys zs = contains' xs (ys ++ xs ++ zs) == True

{-# ANN propAppendAssoc Prop #-}
propAppendAssoc :: String -> String -> String -> Bool
propAppendAssoc xs ys zs = myAppend xs (myAppend ys zs) == myAppend (myAppend xs ys) zs

{-# ANN propAppendNilLeft Prop #-}
propAppendNilLeft :: String -> Bool
propAppendNilLeft xs = myAppend [] xs == xs

{-# ANN propAppendNilRight Prop #-}
propAppendNilRight :: String -> Bool
propAppendNilRight xs = myAppend xs [] == xs

{-# ANN propReverseInvolute (PropWithConfig "--smt cvc5") #-}
propReverseInvolute :: String -> Bool
propReverseInvolute xs = myReverse (myReverse xs) == xs

{-# ANN propReverseAppend Prop #-}
propReverseAppend :: String -> String -> Bool
propReverseAppend xs ys = myReverse (myAppend xs ys) == myAppend (myReverse ys) (myReverse xs)

{-# ANN propReverseSingleton Prop #-}
propReverseSingleton :: Char -> Bool
propReverseSingleton x = myReverse [x] == [x]

{-# ANN propMatchPrefixMyAppend Prop #-}
propMatchPrefixMyAppend :: String -> String -> Bool
propMatchPrefixMyAppend xs ys = matchPrefix xs (myAppend xs ys) == True

{-# ANN propContainsMyAppend (PropWithConfig "--smt cvc5") #-}
propContainsMyAppend :: String -> String -> Bool
propContainsMyAppend xs ys = contains' xs (myAppend xs ys) == True && contains' ys (myAppend xs ys) == True

-- {-# ANN propReverseContains (PropWithConfig "--smt cvc5") #-}
-- propReverseContains :: String -> String -> Bool
-- propReverseContains xs ys = contains' xs ys == contains' (myReverse xs) (myReverse ys)
