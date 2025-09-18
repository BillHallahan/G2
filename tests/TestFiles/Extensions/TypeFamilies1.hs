{-# LANGUAGE DataKinds, TypeFamilies #-}

module TypeFamilies1 where

import Data.Kind

type family F a where
    F Int = Bool
    F Bool = Int

data C a where
    I :: C Int
    B :: C Bool 

f :: C a -> F a
f I = True
f B = 0

f2 :: C a -> F a -> F a
f2 I x = x
f2 B x = x

f3 :: C a -> F a -> F a
f3 I x = not x
f3 B x = x + 1

type family G a
    
g :: C a -> G a
g I = True
g B = 0

type instance G Int = Bool
type instance G Bool = Int

type family H a b where
    H Int (k, v) = k
    H Bool (k, v) = v

h :: C a -> (k, v) -> H a (k, v)
h I (k, _) = k
h B (_, v) = v

newtype Age = Age Int deriving (Eq, Show)

type family N a where
    N Int = Age

age1 :: Int -> N Int
age1 x = Age x

age2 :: a ~ Int => a -> N a
age2 x = Age x

-------------------------------------------------------------------------------
-- Vecs

data Nat = Zero | Succ Nat

type SNat :: Nat -> Type
data SNat n where
    SZero :: SNat Zero
    SSucc :: SNat n -> SNat (Succ n)

deriving instance Eq (SNat n)

type Vec :: Nat -> Type -> Type
data Vec n a where
    Nil  :: Vec Zero a
    (:>) :: a -> Vec n a -> Vec (Succ n) a
infixr 5 :>

deriving instance Eq a => Eq (Vec n a)

type (+) :: Nat -> Nat -> Nat
type family a + b where
    Zero + b = b
    Succ a + b = Succ (a + b)

app :: Vec n a -> Vec m a -> Vec (n + m) a
Nil `app` ys = ys
(x :> xs) `app` ys = x :> (xs `app` ys)

zipDouble :: Vec m a -> Vec n a -> Vec (m + n) b -> Vec (m + n) (a, b)
zipDouble Nil ys v = vecZip ys v
zipDouble (x :> xs) ys (z :> zs) = (x, z) :> (zipDouble xs ys zs)

vecZip :: Vec n a -> Vec n b -> Vec n (a, b)
vecZip Nil _ =  Nil 
vecZip (x :> xs) (y :> ys) = (x, y) :> vecZip xs ys
