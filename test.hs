conTaker1 :: String -> String -> (Int, String)
conTaker1 xs ys =
    case take 18 xs ++ take 18 ys of
        zs@"It" | length xs > 18 -> (2, zs)
        zs -> (4, zs)

-- Doubles1.hs
decodeFloatConst :: [(Integer, Int)]
decodeFloatConst = map decodeFloat ([-9, -8, -7] :: [Double])

decodeFloatConstOriginal :: [(Integer, Int)]
decodeFloatConstOriginal = map decodeFloat ([-10, -9, -8, -7, -6, -5, -4, -3, -2, -1,
                                       0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Double])

decodeFloatSingle :: (Integer, Int)
decodeFloatSingle = decodeFloat (10 :: Double)