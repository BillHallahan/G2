{-# LANGUAGE PatternSynonyms #-}

module PatternSynonyms1 where

pattern NineInt :: Int
pattern NineInt = 9

isNineInt :: Int -> Bool
isNineInt NineInt = True
isNineInt _ = False

pattern NineInteger :: Integer
pattern NineInteger = 9

isNineInteger :: Integer -> Bool
isNineInteger NineInteger = True
isNineInteger _ = False

pattern NineFloat :: Float
pattern NineFloat = 9

isNineFloat :: Float -> Bool
isNineFloat NineFloat = True
isNineFloat _ = False

data Ty = App String [Ty] deriving Eq

pattern Int = App "Int" []
pattern Arrow t1 t2 = App "->" [t1, t2]

isFunc :: Ty -> Bool
isFunc (Arrow _ _) = True
isFunc _ = False

funcArg :: Ty -> Maybe Ty
funcArg (Arrow t _) = Just t
funcArg _ = Nothing

consArrow :: Ty -> Ty -> Ty
consArrow = Arrow