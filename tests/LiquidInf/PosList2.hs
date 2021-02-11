{-@ LIQUID "--no-termination" @-}

module PosList where

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ filterAndSum :: List { x:Int | x >= 0 } -> List { y:Int | y >= 0  } @-}
filterAndSum :: List Int -> List Int
filterAndSum xs = filterPos xs

{-@ filterPos :: List Int -> List Int @-}
filterPos :: List Int -> List Int
filterPos _ = Emp