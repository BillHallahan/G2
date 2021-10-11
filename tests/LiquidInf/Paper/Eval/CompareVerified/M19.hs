{-@ LIQUID "--no-termination" @-}

module M19 (main) where

{-@ main :: { n:Int | n >= 0 } -> { m:Int | m >= 0 && m < n } -> { b:Bool | b } @-}
main :: Int -> Int -> Bool
main n m =
    case while n m (0, m) of
        (_, y') -> n == y'

{-@ while :: n:Int
          -> m:{ m:Int | m < n }
          -> t:{ t:({x:Int | x <= n }, Int) | (fst t < m => snd t = m)
                                           && (fst t >= m => snd t == fst t)  }
          -> (Int, { y:Int | y == n }) @-}
while :: Int -> Int -> (Int, Int) -> (Int, Int)
while n m (x, y) =
    if x < n then while n m (x + 1, if x + 1 > m then y + 1 else y) else (x, y)