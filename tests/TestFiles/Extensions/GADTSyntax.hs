{-# LANGUAGE GADTs #-}

module GADTSyntax where

data MyList a where
  Nil :: MyList a
  (:>) :: a -> MyList a -> MyList a

infixr 1 :>

cons3 :: Int -> MyList Int
cons3 x = x :> x + 1 :> x + 2 :> Nil