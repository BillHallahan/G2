module ListCallStack where

headOf :: [Int] -> Int
headOf = head

tailOf :: [Int] -> [Int]
tailOf = tail

indexOf :: [Int] -> Int
indexOf qs = qs !! 0

lastOf :: [Int] -> Int
lastOf = last

initOf :: [Int] -> [Int]
initOf = init

cycleOf :: [Int] -> Bool
cycleOf xs = case cycle xs of x:_:_:w:_ -> x == w; _ -> error "impossible"