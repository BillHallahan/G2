{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module MiniLib where

import G2.QuasiQuotes.G2Rep

import Data.Data

addTwo :: Int -> Int
addTwo = (+ 2)

bothTrue :: Bool -> Bool -> Bool
bothTrue = (&&)

data InfList a = InfCons a (InfList a) deriving (Show, Data)

$(derivingG2Rep ''InfList)

repeatInf :: a -> InfList a
repeatInf x = InfCons x (repeatInf x)

headInf :: InfList a -> a
headInf (InfCons x _) = x

tailInf :: InfList a -> InfList a
tailInf (InfCons x xs) = xs