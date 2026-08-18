module ADTLitTableStrict where

-- CONFIG: --smt-lists --strict-strings --smt-lams --lit-tables --smt-tuples --smt-adts AB,Maybe

data AB = A | B deriving Eq

takeWhile1 :: Int -> Int -> AB -> [(Int, Int)] -> (Int, [(Int, Int)])
takeWhile1 a b m xs =
    let
        ys = takeWhile (\(x, _) -> case m of
                                        A -> x > 4
                                        B -> x < 2) ((a + 1, b + 2):xs)
    in
    case ys of
        [] -> (1, ys)
        _:_ -> (2, ys)

takeWhile2 :: AB -> [(Int, Int)] -> [(Int, Int)] -> (Int, [(Int, Int)])
takeWhile2 m xs ys =
    let
        zs = takeWhile (\(x, _) -> case m of
                                        A -> x > 4
                                        B -> x < 2) (xs ++ ys)
    in
    case zs of
        [] -> (1, ys)
        _:_ -> (2, ys)


map1 :: AB -> [AB] -> (Int, [AB])
map1 ab xs =
    let
        ys = map (\ab -> case ab of
                            A -> B
                            B -> A) (xs ++ [ab])
    in
    case ys of
        [] -> (1, ys)
        [_] -> (2, ys)
        (_:_) -> (3, ys)
