module IntFuncArg (caller) where

caller :: Int -> Int
caller = call pass

{-@ call :: (Int -> { r:Int | r > (- 8) }) -> Int -> Int @-}
call :: (Int -> Int) -> Int -> Int
call f x = f x

pass :: Int -> Int
pass x = x