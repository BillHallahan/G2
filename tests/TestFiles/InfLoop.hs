module InfLoop where

data M = T (M -> M)

instance Eq M where
    T _ == T _ = True

f f1 t@(T trL) x = f1 x // t

infixl 8 //

(//) :: a -> c -> c
x // f = undefined

