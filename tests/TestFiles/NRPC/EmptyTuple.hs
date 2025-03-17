module EmptyTuple where

import G2.Symbolic

main = assertIO (g [])

g :: [Int] -> Bool
g (w:ws) = g ws
