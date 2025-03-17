module EmptyTuple where

main :: () -> ()
main _ = (g []) `seq` ()

g :: [Int] -> Bool
g (w:ws) = g ws