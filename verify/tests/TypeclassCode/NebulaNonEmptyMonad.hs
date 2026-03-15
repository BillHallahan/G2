{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module TypeclassCode.NebulaNonEmptyMonad where

import Prelude (Bool (..))

data List a = a :> List a | Nil
infixl 4 :>

data NonEmpty a = a :| List a

infixr 5 :|

(++) :: List a -> List a -> List a
(++) Nil     ys = ys
(++) (x :> xs) ys = x :> (xs ++ ys)

(a :| as) <> ~(b :| bs) = a :| (as ++ (b :> bs))

mapList :: (a -> b) -> List a -> List b
mapList _ Nil     = Nil
mapList f (x:>xs) = f x :> mapList f xs

fmap :: (a -> b) -> NonEmpty a -> NonEmpty b
fmap f (a :| as) = f a :| mapList f as

id :: a -> a
id x = x

(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

-- Applicative laws
pureNonEmpty x    = x :| Nil

($) :: (a -> b) -> a -> b
f $ x = f x

(<*>) :: NonEmpty (a -> b) -> NonEmpty a -> NonEmpty b
m1 <*> m2 = (>>==) m1 (\x1 -> (>>==) m2 (\x2 -> (x1 x2) :| Nil))

-- Definition found following the same method as (<*>)
-- ghci> ([1..10] >>= (\y -> [y + 1, y * 2, y + 18])) == ([1..10] >>== (\y -> [y + 1, y * 2, y + 18]))
-- True
(>>=) :: List a -> (a -> List b) -> List b
(>>=) xs'7 f'118 = ds'37 xs'7 f'118

ds'37 :: List t -> (t -> List a) -> List a
ds'37 ds1'28 f'118 = case ds1'28 of
            Nil  -> Nil
            ds3'5 :> ds4'4 -> ds5'4 (f'118 ds3'5) f'118 ds4'4

ds5'4 :: List a -> (t -> List a) -> List t -> List a
ds5'4 ds6'4 f'118 ds4'4 = case ds6'4 of
                        Nil  -> ds'37 ds4'4 f'118
                        ds8'3 :> ds9'3 -> ds8'3:>(ds5'4 ds9'3 f'118 ds4'4)

return :: a -> NonEmpty a
return x = x :| Nil

(>>==) :: NonEmpty a -> (a -> NonEmpty b) -> NonEmpty b
(a :| as) >>== f = case f a of
                        b :| bs -> b :| (bs ++ (as >>= ((\(c :| cs) -> c :> cs) . f)))
