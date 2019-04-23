{-# LANGUAGE QuasiQuotes #-}

module Main where

import G2.Interface
import G2.Language.Syntax
import G2.QuasiQuotes.QuasiQuotes

import Data.List

main :: IO ()
main = do
    r <- f 8 10
    case r of
        Just r' -> print (conc_args r')
        Nothing -> putStrLn $ "Nothing"

    -- print nub_call

f :: Int -> Int -> IO (Maybe (ExecRes ()))
f = [g2|\y z -> \x ? x + 2 == y + z |]

-- nub_call :: Expr
-- nub_call = [g2| nub [1, 2, 3] |]