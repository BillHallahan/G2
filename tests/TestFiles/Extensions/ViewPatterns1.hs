{-# LANGUAGE ViewPatterns #-}

module ViewPatterns1 where

data Shape = Triangle | Rectangle | Square

strToShape :: Char -> Maybe Shape
strToShape 't' = Just Triangle
strToShape 'r' = Just Rectangle
strToShape 's' = Just Square
strToShape _ = Nothing

sides :: Shape -> Int
sides Triangle = 3
sides Rectangle = 4
sides Square = 4

printNumber :: Int -> String
printNumber 3 = "three"
printNumber 4 = "four"
printNumber _ = error "printNumber: number not supported"

shapeToNumSides :: Char -> String
shapeToNumSides (fmap sides . strToShape -> Just x) = printNumber x
shapeToNumSides _ = "shape not recognized"