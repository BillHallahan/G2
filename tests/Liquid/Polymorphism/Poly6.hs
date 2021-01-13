module Prop6 where

{-@ type TRUE = {v:Bool | v} @-}

data List a = Emp | C a

{-@ measure size :: List a -> Int
    size (Emp) = 0
    size (C x) = 1
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ f :: List Int -> TRUE @-}
f :: List Int -> Bool
f xs =
    let
        l1 = len xs
        l2 = len (g xs)
    in
    case l1 of
        0 -> case l2 of { 0 -> True; _ -> False}
        1 -> case l2 of { 1 -> True; _ -> False}
        _ -> False

{-@ len :: xs:List a -> { r:Int | size xs == r } @-}
len :: List a -> Int
len Emp = 0
len (C x) = 1

g :: List a -> List a
g x = x