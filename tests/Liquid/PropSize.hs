{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-} 

module PropSize where

infixr 9 :+:

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ badLength :: l:List a -> {v:Int | l = l} @-} 
badLength            :: List a -> Int
badLength Emp        = 0
badLength (x :+: xs) = 1

{-@ prop_size :: TRUE @-}
prop_size  = lAssert (badLength l1 == 1)

{-@ l1 :: List Int @-}
l1 :: List Int
l1 = 1 :+: Emp

{-@ type TRUE = {v:Bool | v} @-}

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)