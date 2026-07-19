module ADTLitTable where

-- CONFIG: --smt-lists --smt-lams --lit-tables --smt-adts AB,Maybe

data AB = A | B deriving Eq

takeWhile1 :: AB -> [Int] -> (Int, [Int])
takeWhile1 m xs =
    let
        ys = takeWhile (\x -> case m of
                                A -> x > 4
                                B -> x < 2) xs
    in
    case ys of
        (5:_) -> (1, ys)
        (1:_) -> (2, ys)
        [] -> (3, ys)
        _ -> (4, ys)

takeWhile2 :: Maybe AB -> [Int] -> (Int, [Int])
takeWhile2 m xs =
    let
        ys = takeWhile (\x -> case m of
                                Just _ -> x > 4
                                Nothing -> x < 2) xs
    in
    case ys of
        (5:_) -> (1, ys)
        (1:_) -> (2, ys)
        [] -> (3, ys)
        _ -> (4, ys)

takeWhile3 :: Int -> [AB] -> (Int, [AB])
takeWhile3 x xs =
    let
        ys = takeWhile (\ab -> case ab of
                                A -> True
                                B -> x < 2) xs
    in
    case ys of
        (A:_) -> (1, ys)
        (B:_) -> (2, ys)
        [] -> (3, ys)

map1 :: [AB] -> (Int, [AB])
map1 xs =
    let
        ys = map (\ab -> case ab of
                            A -> B
                            B -> A) xs
    in
    case ys of
        [_] -> (1, ys)
        (A:_) -> (2, ys)
        (B:A:B:_) -> (3, ys)
        (B:A:A:_) -> (4, ys)
        (B:B:_) -> (5, ys)
        (B:_) -> (6, ys)
        [] -> (7, ys)


takeWhile5 :: Maybe Int -> [Int] -> (Int, [Int])
takeWhile5 m xs =
    let
        ys = takeWhile (\x -> x < 2) xs
    in
    case length ys > 4 of
        True -> (1, ys)
        False -> (2, ys)