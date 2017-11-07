module Error3 where

f :: Int -> Int
f x = 
    case (error "Error") of
        0 -> 1
        1 -> 1