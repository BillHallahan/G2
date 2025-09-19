{-# LANGUAGE TypeFamilies #-}

module DataFamilies1 where

data family A a

data instance A Int = AI Int
data instance A Float = AF Float

f :: A Int -> Int
f (AI x) = x

-- Adapted from https://wiki.haskell.org/index.php?title=GHC/Type_families

-- Declare a list-like data family
class AdaptList a where
    data XList a
    app :: XList a -> XList a -> XList a

-- Declare a list-like instance for Char
instance AdaptList Char where
    data XList Char = XCons Char (XList Char) | XNil
    app XNil ys = ys
    app (XCons c xs) ys = XCons c (app xs ys)

-- Declare a number-like instance for ()
instance AdaptList () where
    data XList () = XListUnit !Int
    app (XListUnit n1) (XListUnit n2) = XListUnit (n1 + n2)

app3 :: AdaptList a => XList a -> XList a -> XList a -> XList a
app3 xs ys zs = app xs (app ys zs)

app3Char :: XList Char -> XList Char -> XList Char -> XList Char
app3Char = app3

app3Unit :: XList () -> XList () -> XList () -> XList ()
app3Unit = app3