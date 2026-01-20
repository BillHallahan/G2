module Test where

f1 :: String -> String -> String -> String
f1 xs ys zs = xs ++ ys ++ zs

f2 :: String -> String -> Int
f2 xs ys = length xs + length ys

f3 :: String -> String -> Bool
f3 xs ys = take (length xs) ys == xs 

f4 :: String -> String -> Bool
f4 [] [] = True
f4 _ [] = False
f4 xs ys@(_:ys') | take (length xs) ys == xs = True
                 | otherwise = f4 xs ys'

f5 :: String -> String -> String -> (String, String)
f5 xs ys zs = (xs ++ ys, ys ++ zs)

f6 :: String -> Maybe String
f6 [] = Nothing
f6 (x:xs) = Just xs

f7 :: String -> String -> Maybe (Either String String)
f7  x y | x < y = Just $ Left x
        | y < x = Just $ Right y
        | otherwise = Nothing

f8 :: String -> String -> Either String String
f8  x y | x < y = Left x
        | y < x = Right y
        | otherwise = error "f8"