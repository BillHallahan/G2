-- cmd_line = (--no-keep-quals)

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined (appF) where

appF :: Int
appF = f 1

f :: Int -> Int
f x = if x >= 0 then 1 else die ""

{-@ die :: { s:String | false } -> Int @-}
die :: String -> Int
die = error