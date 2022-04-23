module AbsTypeClassVerified where

{-@ callF :: Int -> { xs:[Int] | len xs == 1 }@-}
callF :: Int -> [Int]
callF x = f x x

{-@ class Test t where
		f :: forall a . t -> a -> { xs:[a] | len xs == 1 }
		g :: t -> Int @-}
class Test t where
    f :: t -> a -> [a]
    
    g :: t -> Int

instance Test Int where
    f _ x = [x]
    g _ = 0
