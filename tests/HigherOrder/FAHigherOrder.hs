module FAHigherOrder where

test1 :: (Int -> Int -> Int) -> Int -> Int
test1 g x = g (error "BAD") x

test2 :: (Int -> Int -> Int) -> Int -> Int
test2 g x =
    case g 3 7 of
        1 -> 1
        _ -> case g (error "BAD") x of
                    2 -> 2
                    _ -> 3

test3 :: (Int -> Int -> Int) -> Int -> Int
test3 g x =
    case g (error "BAD") x of
        1 -> 1
        _ -> case g 3 7 of
                    2 -> 2
                    _ -> 3

test4 :: ([Int] -> Int -> Int) -> Int -> Int
test4 g x =
    case g [1, 2, 3, 4, error "BAD"] x of
        1 -> 1
        _ -> case g [1, 2, 3, 4, 5] 7 of
                    2 -> 2
                    _ -> 3

test5 :: ([Int] -> Int -> Int) -> Int -> Int
test5 g x =
    case g [1, 2, 3, 4, 5] 7 of
        1 -> 1
        _ -> case g [1, 2, 3, 4, error "BAD"] x of
                    2 -> 2
                    _ -> 3

test6 :: ((Int -> Int) -> Int -> Int) -> Int -> Int
test6 g x =
    case g (\x -> x + 1) x of
        1 -> 1
        _ -> case g (\_ -> error "error") 7 of
                    2 -> 2
                    _ -> 3

test7 :: ((Int -> [Int]) -> Int -> Int) -> Int -> Int
test7 g x =
    case g (\x -> [x + 1]) x of
        1 -> 1
        _ -> case g (\_ -> [1, 2, error "error"]) 7 of
                    2 -> 2
                    _ -> 3

test8 :: ((Int -> [Int]) -> [Int] -> Int -> Int) -> Int -> Int
test8 g x =
    case g (\x -> [x + 1]) [] x of
        1 -> 1
        _ -> case g (\_ -> [1, 2, error "error"]) (1:error "error") 7 of
                    2 -> 2
                    _ -> 3

test9 :: (a -> a -> a) -> a -> [a] -> Int -> a
test9 f _ (x:y:_) z =
    f x (if z > 0 then y else error "here")
test9 f d _ _ = d
