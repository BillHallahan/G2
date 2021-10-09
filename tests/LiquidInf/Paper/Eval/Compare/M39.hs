{-@ LIQUID "--no-termination" @-}

module M39 (main) where

data Peano = Succ Peano | Nil

{-@ main :: Peano -> Int -> (Int, Int, Int, Int) @-}
main :: Peano -> Int -> (Int, Int, Int, Int)
main xs maxPathLen 
    | maxPathLen > 0 = breakWhile xs (0, 0, 0 + (maxPathLen + 1) - 1, maxPathLen)
    | otherwise = (0, 0, 0, 0)

{-@ breakWhile :: Peano -> (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
breakWhile :: Peano -> (Int, Int, Int, Int) -> (Int, Int, Int, Int)
breakWhile xs (glob3_dc, glob3_pathend_off, glob3_pathlim_off, maxPathLen) =
    if glob3_pathend_off + glob3_dc >= glob3_pathlim_off
        then (glob3_dc, glob3_pathend_off, glob3_pathlim_off, maxPathLen)
        else (if isSucc xs
                    then breakWhile (peanoTail xs) (body (glob3_dc, glob3_pathend_off, glob3_pathlim_off, maxPathLen))
                    else body ((glob3_dc, glob3_pathend_off, glob3_pathlim_off, maxPathLen)))

{-@ body :: (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
body :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
body (glob3_dc, glob3_pathend_off, glob3_pathlim_off, maxPathLen) =
    case 0 <= glob3_dc + 1 && glob3_dc + 1 < maxPathLen + 1 of
                True -> (glob3_dc + 1, glob3_pathend_off, glob3_pathlim_off, maxPathLen)
                False -> die "bad"

isSucc :: Peano -> Bool
isSucc (Succ _) = True
isSucc _ = False

peanoTail :: Peano -> Peano
peanoTail (Succ ys) = ys
peanoTail _ = Nil

{-@ die :: {v:String | false} -> a @-}
die str = error str
