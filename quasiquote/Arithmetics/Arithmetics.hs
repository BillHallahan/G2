{-# LANGUAGE QuasiQuotes #-}

module Arithmetics.Arithmetics where

import Arithmetics.Interpreter
import G2.QuasiQuotes.QuasiQuotes

triplesTo30 :: IO (Maybe (Expr, Expr, Expr))
triplesTo30 =
  [g2| \(a :: Int) -> ?(x :: Expr)
                      ?(y :: Expr)
                      ?(z :: Expr) |
  (snd $ eval [] (Mul x (Mul y z))) == 30|] 0
