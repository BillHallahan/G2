module ImportTest where 

import Import 

{-# RULES
"simplifyAdd1" forall x . myId (add1 x) = x + 1
 
"importTypes" forall x . foo (MkSomeType x) = x * 2
 
  #-}

myId :: a -> a
myId x = x


{-# NOINLINE foo #-}
foo :: SomeType->Int 
foo (MkSomeType x) = x 


{-# NOINLINE callAdd1 #-}
callAdd1 :: Int -> Int
callAdd1 x = 1 + add1 x