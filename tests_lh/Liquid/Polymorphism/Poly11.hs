module Poly11 where

{-@ call :: Bool -> [{v:Bool | v }] @-}
call :: Bool -> [Bool]
call cs = called (\_ -> higher cs)

called :: Ord k => (Int -> k) -> [k]
called f = [f 1]

-- {-@ higher :: Bool -> {v:Bool | v } @-}
higher :: Bool -> Bool
higher centers = True