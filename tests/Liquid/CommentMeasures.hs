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

data CPoly a b = CPoly1 a | CPoly2 b


