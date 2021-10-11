{-@ LIQUID "--no-termination" @-}

module M32 (main) where

{-@ main :: Bool -> Int -> { b:Bool | b } @-}
main :: Bool -> Int -> Bool
main b ij = case while 100 (b, ij, ij, 0) of
                (b', i, j, n) -> i == j

{-@ while :: k:Int
          -> t:{ t:(Bool, Int, Int, Int) | ((2 * k - x_Tuple44 t) mod 2 = 0 => x_Tuple42 t == x_Tuple43 t)
                                         && (
                                                    (2 * k - x_Tuple44 t) mod 2 = 1 =>
                                                        (
                                                            (x_Tuple42 t + 1 == x_Tuple43 t && x_Tuple41 t)
                                                        ||  
                                                            (x_Tuple42 t - 1 == x_Tuple43 t && not (x_Tuple41 t))
                                                        )
                                            )
                                         && x_Tuple44 t <= 2 * k }
          -> { t:(Bool, Int, Int, Int) | x_Tuple42 t == x_Tuple43 t } @-}
while :: Int -> (Bool, Int, Int, Int) -> (Bool, Int, Int, Int)
while k (b, i, j, n) =
    if n < 2 * k
        then while k (not b, if b then i + 1 else i, if not b then j + 1 else j, n + 1)
        else (b, i, j, n)