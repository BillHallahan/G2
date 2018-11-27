module Ordering where

data X = X | Y

{-@ measure isX @-}
isX :: X -> Bool
isX X = True
isX Y = False

{-@ measure isY @-}
isY :: X -> Bool
isY Y = True
isY X = False

{-@ f :: x:X -> { y:X | x == y } @-}
f :: X -> X
f X = X
f Y = Y

{-@ lt :: x:{ xi:X | isX xi } -> { y:X | x < y} @-}
lt :: X -> X
lt x = Y

{-@ gt :: x:{ xi:X | isX xi } -> { y:X | x > y} @-}
gt :: X -> X
gt x = Y

{-@ ge :: x:{ xi:X | isX xi } -> { y:X | isX y && x == y} @-}
ge :: X -> X
ge x = X

{-@ oneOrOther :: x:X -> { y:X | x >= y || x <= y} @-}
oneOrOther :: X -> X
oneOrOther x = Y
