-- cmd_line = (--no-keep-quals)

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined (appF) where

appF :: Int
appF = f 1 2

f :: Int -> Int -> Int
f x y = if x == y then 1 else die ""

{-@ die :: { s:String | false } -> Int @-}
die :: String -> Int
die = error