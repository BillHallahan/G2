module Error3 where

f :: Int -> Int
f x = 
    case (error "Error") of
        0 -> 1
        1 -> 1

g :: Int -> Int
g x =
	case (error "Error") of
		_ -> 1