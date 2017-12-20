module Error3 where

f :: Int -> Int
f x = 
	-- GHC trats this as pattern matching on Integers not Ints
    case (error "Error") of
        0 -> 1
        1 -> 1

g :: Int -> Int
g x =
  case (error "Error") of
    _ -> 1
