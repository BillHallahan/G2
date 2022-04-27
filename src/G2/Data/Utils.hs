module G2.Data.Utils (fst3, uncurry3, uncurry4) where

fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

uncurry4 :: (a -> b -> c -> d -> e) -> ((a, b, c, d) -> e)
uncurry4 f (a,b,c,d) = f a b c d
