module PolyDataTy1 where

data X a = X a | Y

f :: Int -> X Int -> Int
f _ (X x) = x
f x Y = x

data CThreeOpt a b c = Fst a | Snd b | Thd c

getFst :: CThreeOpt a b c -> a
getFst (Fst x) = x
getFst _ = error "getFst: not passed Fst"

getFstXIntInt :: CThreeOpt (X Float) Int Int -> X Float
getFstXIntInt x = getFst x

getSndDef :: CThreeOpt a b c -> b -> b
getSndDef (Snd x) _ = x
getSndDef _ x = x

getSndDefXIntInt :: CThreeOpt (X Float) Int Int -> Int -> Int
getSndDefXIntInt = getSndDef

data Groups a b c d e f g h = Five a b c d e | Six a b c d e f | Seven a b c d e f g | Eight a b c d e f g h
data Z = Z

sum :: Groups Int Int Int Int Int Int Z Z -> Int
sum (Five a b c d e) = a + b + c + d + e
sum (Six a b c d e f) = a + b + c + d + e + f
sum _ = error "sum: Can't sum X"