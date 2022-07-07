{-@ LIQUID "--no-termination" @-}

module Queen (main) where

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error str

assertIO :: Bool -> IO ()
assertIO True = return ()
assertIO _ = die "violated assert"

{-@ assert :: TRUE -> a -> a @-}
assert :: Bool -> a -> a
assert True x = x
assert _ _ = die "violated assert"

dotsPrint :: Int -> IO ()
dotsPrint n = if n == 0 then return () else do putStr "."; dotsPrint (n - 1)

queenPrint :: Int -> Int -> (Int -> Int) -> IO ()
queenPrint size n queenArray = do
    let get i n map = map i
        aux row = if row == size
                        then return ()
                        else do
                            assertIO (0 <= row)
                            let m = get row n queenArray
                            dotsPrint (m - 1)
                            putStr "Q"
                            dotsPrint (size - m)
                            putStr "\n"
                            aux (row + 1)
    aux 0
    putStr "\n"

loop :: Int -> Int -> Int -> (Int -> Int) -> IO ()
loop row size n queenArray = do
    let test j n queenArray = let
            get i n map = map i
        
            qj = get j n queenArray
            aux i = if i < j then
                            let
                                qi = get i n queenArray
                            in
                            assert (0 <= i)
                                (if qi == qj then False else if abs (qj - qi) == j - i then False else aux (i + 1))
                        else True
                                    in
                                    assert (0 <= j) (aux 0)
    let get i n map = map i
    let update i x n map = \j -> if i == j then x else map j

    let assign n queenArray i j = update i j n queenArray
    assertIO (0 <= row)
    let next = get row n queenArray + 1
    if next > size then do
        let queenArray' = assign n queenArray row 0
        if row == 0 then return () else loop (row - 1) size n queenArray'
    else do
        let queenArray' = assign n queenArray row next
        if test row n queenArray' then
                if row + 1 == size then do
                    queenPrint size n queenArray'
                    loop row size n queenArray'
                else loop (row + 1) size n queenArray'
        else loop row size n queenArray'

main :: Int -> IO ()
main size = do
    let make_vect n s = \i -> s
    let queenArray = make_vect size 0
    if size > 0 then loop 0 size size queenArray else return ()