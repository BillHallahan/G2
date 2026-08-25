module Uninterpreted where

-- CONFIG: --smt-lists --smt-lams --lit-tables --smt-tuples --smt-adts AB,Maybe --higher-order uninterpreted

data AB = A | B deriving Eq

call1 :: (AB -> AB) -> AB -> Int
call1 f ab =
    case ab of
        A -> case f ab of
                A -> 1
                B -> 2
        B -> case f ab of
                A -> 3
                B -> 4

call2 :: (AB -> AB) -> AB -> Int
call2 f ab =
    case ab of
        A -> case f ab of
                A -> case f B of
                        A -> 1
                        B -> 2
                B -> case f B of
                        A -> 3
                        B -> 4
        B -> case f ab of
                A -> case f A of
                        A -> 5
                        B -> 6
                B -> case f A of
                        A -> 7
                        B -> 8

call3 :: (AB -> AB) -> AB -> Int
call3 f x = case f (case x of A -> B; B -> A) of
                A -> 1
                B -> 2

map1 :: (AB -> AB) -> [AB] -> (Int, [AB])
map1 f xs =
    let
        ys = map f xs
    in
    case ys of
        [] -> (1, ys)
        (A:_) -> case xs of
                    B:_ -> (2, ys)
                    _ -> (3, ys)
        _ -> (4, ys)

map2 :: (AB -> AB) -> [AB] -> [AB] -> (Int, [AB])
map2 f xs ys =
    let
        zs = map f (xs ++ ys)
    in
    case zs of
        [] -> (1, zs)
        (A:_) -> case xs of
                    B:_ -> (2, zs)
                    [] -> case ys of
                            B:_ -> (3, zs)
                            _ -> (4, zs)
                    _ -> (5, zs)
        _ -> (6, zs)

map3 :: (AB -> AB) -> (AB -> AB) -> [AB] -> [AB] -> (Int, [AB])
map3 f g xs ys =
    let
        ws = map f (xs ++ ys)
        zs = map g (xs ++ ys)
        ws_zs = map (f . g) xs
    in
    case zs of
        [] -> (1, zs)
        (A:_) -> case ws_zs of
                    B:_ -> (2, zs)
                    [] -> case ys of
                            B:_ -> (3, zs)
                            _ -> (4, zs)
                    _ -> (5, zs)
        _ -> (6, zs)
