{-# LANGUAGE QuasiQuotes #-}

module Simple.SimpleTest1 where

import Simple.Simple1
import G2.QuasiQuotes.QuasiQuotes

import RegEx.RegEx as R

sd :: () -> IO (Maybe Expr)
sd =
    [g2| \(e :: ()) -> ?(func :: Expr) | eval (App func num1) == num1 |]

af :: Expr -> Bool
af func = (eval (App func num1)) == num1
