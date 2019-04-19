{-# LANGUAGE QuasiQuotes #-}

module Main where

import G2.Language.Syntax
import G2.Translation.QuasiQuotes

import Data.List

main :: IO ()
main = do
    print f

    -- print nub_call

f :: Expr
f = [g2|\y z -> \x ? x + 2 == y + z |]

-- nub_call :: Expr
-- nub_call = [g2| nub [1, 2, 3] |]