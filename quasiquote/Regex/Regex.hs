{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Regex.Regex where

import Data.Data
import G2.QuasiQuotes.G2Rep

data Regex = Epsilon | Atom Char | Star Regex
    | Concat Regex Regex | Plus Regex Regex
  deriving (Show, Eq, Data)

$(derivingG2Rep ''Regex)

match :: Regex -> [Char] -> Bool
match Epsilon [] = True
match (Atom x) (c:[]) = x == c
match r@(Star x) str =
  match Epsilon str
  || or [match x str1 && match r str2 |
          (str1, str2) <- splits str]
match (Concat r1 r2) str =
  or [match r1 str1 && match r2 str2 |
          (str1, str2) <- splits str]
match (Plus r1 r2) str =
  match r1 str || match r2 str
match _ _ = False

splits :: [a] -> [([a], [a])]
splits str = [splitAt n str | n <- [0..length str]]


