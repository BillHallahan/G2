{-# LANGUAGE QuasiQuotes #-}

module Main where

import G2.Language.Syntax
import G2.QuasiQuotes.QuasiQuotes

import Data.List

main :: IO ()
main = do
    print (f 8 10)

    -- print nub_call

f :: Int -> Int -> [Expr]
f = [g2|\y z -> \x ? x + 2 == y + z |]

-- nub_call :: Expr
-- nub_call = [g2| nub [1, 2, 3] |]