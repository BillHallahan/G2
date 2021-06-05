{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module RegEx.RegEx where

import Data.Data
import G2.QuasiQuotes.G2Rep


data RegEx = Empty | Epsilon | Atom Char
  | Star RegEx | Concat RegEx RegEx | Or RegEx RegEx
  deriving (Show, Eq, Data)

$(derivingG2Rep ''RegEx)

match :: RegEx -> String -> Bool
match Empty _        = False
match Epsilon s      = null s
match (Atom x) s     = s == [x]
match (Star _) []    = True
match r@(Star x) s   = any (match2 x r)
                           (splits [1..length s] s)
match (Concat a b) s = any (match2 a b)
                           (splits [0..length s] s)
match (Or a b) s     = match a s || match b s

match2 :: RegEx -> RegEx -> (String, String) -> Bool
match2 a b (sa, sb)  = match a sa && match b sb

splits :: [Int] -> [a] -> [([a], [a])]
splits ns x = map (\n -> splitAt n x) ns




