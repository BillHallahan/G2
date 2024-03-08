module Show where

show1 :: String
show1 = show (978925 :: Int)

show2 :: String
show2 = show (-978925 :: Int)

show3 :: Int -> String
show3 x | x > 0 = "Pos: " ++ show x
        | x == 0 = "Zero: " ++ show x
        | otherwise = "Neg: " ++ show x

show4 :: Int -> Char
show4 x = case show x of
            y:_ -> y
            [] -> error "HERE"

show5 :: Int -> (String, Char)
show5 x | 10 <= x && x <= 20 = ("10 < x && x < 20: " ++ y, f y)
        | 200 <= x && x <= 300  = ("200 <= x && x < 300: " ++ y, f y)
        | 3000 <= x && x < 4000  = ("3000 <= x && x < 4000: " ++ y, f y)
        | otherwise = ("otherwise: " ++ y, f y)
        where
            y = show x

f :: String -> Char
f ['1', x] = x
f [_, x] = x
f ['2', _, x] = x
f [_, x, _] = x
f ['3', _, _, x] = x
f [_, x, _, _] = x
f (x:_) = x
f [] = error "Empty string"

data WeirdShow = Emp | One | Two | Three | Four

instance Show WeirdShow where
    show Emp = ""
    show One = "a"
    show Two = "aa"
    show Three = "aaa"
    show Four = "aaaa"

checkWS :: WeirdShow -> String
checkWS = show