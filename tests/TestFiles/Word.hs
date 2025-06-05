module Word where

import Data.Word

addWords :: Word -> Word -> (Word, Bool)
addWords x y =
    case x + y < 0 of
        True -> (x + y, False)
        False -> (x + y, True)

subWords1 :: Word -> Word -> (Word, Bool)
subWords1 x y =
    case x - y < 0 of
        True -> (x + y, False)
        False -> (x + y, True)

subWords2 :: Word -> Word -> (Word, Bool)
subWords2 x y =
    case x - y > x of
        True -> (x + y, False)
        False -> (x + y, True)

fromIntegerTest :: Integer -> (Word, Int)
fromIntegerTest x =
    let y = fromInteger x in
    case () of
        () | y < 0 -> (y, 1)
           | y > 10 -> (y, 2)
           | otherwise -> (y, 3)