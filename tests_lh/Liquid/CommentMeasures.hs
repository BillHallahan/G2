module CommentMeasures where

data C = C Int

{-@ measure ge4 :: C -> Bool 
	ge4 (C x) = x >= 4 @-}

{-@ ge4gt5 :: {c:C | ge4 c} -> {x:Int | x > 5 } @-}
ge4gt5 :: C -> Int
ge4gt5 (C x) = 1 + x

{-@ measure t :: C -> Bool
	t (C _) = False @-}

{-@ d :: Int -> {c:C | t c} @-}
d :: Int -> C
d x = C x

{-@ measure unpackCP :: CPoly a -> a
	unpackCP (CP x) = x @-}

data CPoly a = CP a

{-@ unpackCP' :: cp:CPoly a -> {x:a | x == unpackCP cp} @-}
unpackCP' :: CPoly a -> a
unpackCP' (CP x) = x

{-@ unpackBool :: cp:CPoly Bool -> {x:Bool | unpackCP cp} @-}
unpackBool :: CPoly Bool -> Bool
unpackBool (CP x) = x

data OneOf a b = A a | B b

{-@ measure valA :: OneOf a b -> a 
	valA (A a) = a @-}
 
{-@ measure isValA :: OneOf a b -> Bool 
	isValA (A _) = True
	isValA (B _) = False @-}

{-@ getsA :: x:OneOf a b -> {y:a | y == valA x} @-}
getsA :: OneOf a b -> a
getsA (A a) = a
getsA _ = die "Not A"

{-@ getsAInt :: x:OneOf Int Double -> {y:Int | y == valA x} @-}
getsAInt :: OneOf Int Double -> Int
getsAInt (A a) = a
getsAInt _ = die "Not A"

{-@ sumSameOneOfs :: x:OneOf Int Int -> {y:OneOf Int Int | isValA x <=> isValA y} -> Int @-}
sumSameOneOfs :: OneOf Int Int -> OneOf Int Int -> Int
sumSameOneOfs (A a) (A a') = a + a'
sumSameOneOfs (B b) (B b') = b + b'
sumSameOneOfs _ _ = die "A and B given"

{-@ gets2As :: x:OneOf Int Int -> {y:OneOf Int Int | isValA x <=> isValA y} -> Int @-}
gets2As :: OneOf Int Int -> OneOf Int Int -> Int
gets2As (A a) (A a') = a + a'
gets2As _ _ = die "A and B, or 2 Bs, given"

gets2As' :: OneOf Int Int -> OneOf Int Int -> Int
gets2As' (A a) (A a') = a + a'
gets2As' _ _ = die "A and B, or 2 Bs, given"

{-@ die :: {x:String| false} -> a @-}
die :: String -> a
die s = error s

{-@ measure addsToLarger :: C -> Bool
	addsToLarger (C x) = x < x + x @-}

{-@ addsToLarger' :: {c:C | addsToLarger c} @-}
addsToLarger' :: C
addsToLarger' = C 0
