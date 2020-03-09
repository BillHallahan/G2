-- cmd_line = (--no-keep-quals)

{-@ LIQUID "--no-termination" @-}

module PosList () where
	
data D a = Emp | R a deriving (Eq, Ord, Show)

{-@ f :: { y:Int | y >= 0  } @-}
f :: Int
f = g Emp

g :: D Int -> Int
g Emp = 0
g (R x) = x
