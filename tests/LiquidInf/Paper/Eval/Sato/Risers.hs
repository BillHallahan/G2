{-@ LIQUID "--no-termination" @-}

module Risers (main) where

{-@ die :: {v:String | false} -> a @-}
die str = error str

risers :: [Int] -> [[Int]]
risers xs =
    let risersElse x ys = (case ys of
                                [] -> die "empty"
                                s:ss -> [x]:s:ss)
        risersThen x ys = case ys of
                                [] -> die "empty"
                                s:ss -> (x:s):ss
    in
    case xs of
        [] -> []
        [x] -> [[x]]
        x:y:etc ->
            if x < y
                then risersThen x (risers (y:etc))
                else risersElse x (risers (y:etc))

main :: [Int] -> [[Int]]
main m = risers m