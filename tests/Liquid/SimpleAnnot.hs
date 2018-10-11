module SimpleAnnot where

{-@  f :: b -> b @-}
f :: b -> b
f b = b

{-@ simpleF :: { y:Int | y > 0} @-}
simpleF :: Int
simpleF = f 1