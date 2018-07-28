{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}
 

module Error2 where


infixr 9 :+:

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ die :: {v:String | false} -> a @-}
die str = error str

f1 op (x :+: xs) = f op x
f1 op Emp        = die ""

f :: (a -> a -> a) -> a -> a
f op b = b `op` b
