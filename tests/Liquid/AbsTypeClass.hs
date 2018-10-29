module AbsTypeClass where

{-@ callF :: Int -> { xs:[Int] | len xs == 1 }@-}
callF :: Int -> [Int]
callF x = f x x

class Test t where
    f :: t -> a -> [a]

instance Test Int where
    f _ x = [x]