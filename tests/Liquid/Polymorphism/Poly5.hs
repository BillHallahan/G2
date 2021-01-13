module Poly5 where

data C a = Emp | C a

{-@ call :: C Int -> {v:Bool | v} @-}
call :: C Int -> Bool
call Emp = True
call xs = case copy xs of { C _ -> True; _ -> False}

copy   :: C a -> C a
copy Emp = Emp
copy (C x) = C x