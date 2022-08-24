{-@ LIQUID "--no-termination" @-}

module Queen_simple (main) where

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error str

{-@ assert :: TRUE -> a -> a @-}
assert :: Bool -> a -> a
assert True x = x
assert _ _ = die "violated assert"


loop :: [Bool] -> Int -> Int -> Int -> (Int -> Int) -> ()
loop b row size n queenArray =
    let assign n queenArray i j = let
                                    update i x n map = \j -> if i == j then x else map j in
                                    update i j n queenArray
    in
    let get i n map = map i
        next = get row n queenArray + 1 in
    if next > size then
        let queenArray' = assign n queenArray row 0 in
        if row == 0 then () else loop (tl b) (row - 1) size n queenArray'
    else
        let queenArray' = assign n queenArray row next in
        if hd b then
            if row + 1 == size
                    then loop (tl b) row size n queenArray'
                    else loop (tl b) (row + 1) size n queenArray'
        else loop (tl b) row size n queenArray

main :: [Bool] -> Int -> ()
main b size =
    let make_vect n s = \i -> assert (0 <= i && i < n) s
        queenArray = make_vect size 0 in
    if size > 0 && not (null b) then
        loop b 0 size size queenArray
        else ()


hd :: [Bool] -> Bool
hd (x:_) = x
hd [] = True

tl :: [Bool] -> [Bool]
tl (_:xs) = xs
tl [] = []