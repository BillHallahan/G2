module Poly17 where

data List a = Emp | C a

{-@ measure test :: List a -> Bool
        test Emp = True
        test (C _) = False
  @-}

{-@ empty2 :: { xs:List a | test xs } @-}
empty2 :: List a
empty2 = empty

empty :: List a
empty = Emp 