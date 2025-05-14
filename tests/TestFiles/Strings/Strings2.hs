-- !!! Wentworth's version of a program to generate
-- !!! all the expansions of a generalised regular expression
-- !!!
--
-- RJE: Modified so it only outputs the number of characters in the output,
-- rather that the output itself, thus avoiding having to generate such a
-- huge output file to get a reasonable execution time.

module Strings2 where

import Data.Char
import System.Environment

import G2.Symbolic

main = do
  regex <- mkSymbolic
  print (concat (expand' regex))

expand' [] = [""]
expand' ('<':x) = numericRule x
expand' (c:rest) = [ [c] | z <- expand' rest ]

numericRule x
  = [ show i
	| i <- [u..v] ]
  where
    (p,_:q) = span (/= '-') x
    (u,v)   = (0, foldl (\ u c -> u) 0 p)
