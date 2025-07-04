conTaker1 :: String -> String -> (Int, String)
conTaker1 xs ys =
    case take 18 xs ++ take 18 ys of
        zs@"It was a dark and stormy night" | length xs < length ys -> (1, zs)
                                            | length xs > 18 -> (2, zs)
                                            | otherwise -> (3, zs)
        zs -> (4, zs)