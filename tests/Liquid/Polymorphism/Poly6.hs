module Prop6 where

data List a = Emp | C a

{-@ type TRUE = {v:Bool | v} @-}

{-@ f :: List Int -> TRUE @-}
f :: List Int -> Bool
f xs =
    let
        l2 = case g xs of Emp -> 0; _ -> 1
    in
    case xs of
        Emp -> case l2 of { 0 -> True; _ -> False}
        C _ -> case l2 of { 1 -> True; _ -> False}

g :: List a -> List a
g x = x