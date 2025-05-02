module StringCrash where

import Data.Char
import G2.Symbolic

f :: String -> [String]
f x =
    let y = [ pad | i <- [u..u] ] in
    y
  where
    u   = foldl (\ _ c -> ord c) 0 x
    pad  = [ '0' | i <- [1 .. (width-1)]]
    width   = length (show u)


g :: IO [String]
g = do
    s <- getContents
    let mknum = ord (head s)
    let x = [ "0" | i <- [mknum..mknum] ]
    return x