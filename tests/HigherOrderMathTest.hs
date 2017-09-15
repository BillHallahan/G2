module HigherOrderMathTest where

import G2.Internals.Language

import TestUtils

abs2 = Var (Id (Name "abs2" (Just "HigherOrderMath") 0) TyBool) 
square = Var (Id (Name "square" (Just "HigherOrderMath") 0) TyBool) 
negativeSquare = Var (Id (Name "negativeSquare" (Just "HigherOrderMath") 0) TyBool) 
fourthPower = Var (Id (Name "fourthPower" (Just "HigherOrderMath") 0) TyBool) 
add1 = Var (Id (Name "add1" (Just "HigherOrderMath") 0) TyBool) 
sub1 = Var (Id (Name "sub1" (Just "HigherOrderMath") 0) TyBool) 

add = Var (Id (Name "add" (Just "HigherOrderMath") 0) TyBool)
sub = Var (Id (Name "sub" (Just "HigherOrderMath") 0) TyBool)
approxSqrt = Var (Id (Name "approxSqrt" (Just "HigherOrderMath") 0) TyBool)
pythagorean = Var (Id (Name "pythagorean" (Just "HigherOrderMath") 0) TyBool)

notNegativeAt0 = Var (Id (Name "notNegativeAt0" (Just "HigherOrderMath") 0) TyBottom)
notNegativeAt0NegativeAt1 = Var (Id (Name "notNegativeAt0NegativeAt1" (Just "HigherOrderMath") 0) TyBottom)

abs2NonNeg :: [Expr] -> Bool
abs2NonNeg [f, (Lit (LitDouble x))] = f `eqIgT` abs2 && x >= 0
abs2NonNeg _ = False

squareRes :: [Expr] -> Bool
squareRes [f, (Lit (LitDouble x))] = f `eqIgT` square && (x == 0 || x == 1)
squareRes _ = False

negativeSquareRes :: [Expr] -> Bool
negativeSquareRes [f] = f `eqIgT` negativeSquare
negativeSquareRes _ = False

fourthPowerRes :: [Expr] -> Bool
fourthPowerRes [f, (Lit (LitDouble x))] = f `eqIgT` square && (x == 0 || x == 1)
fourthPowerRes _ = False

addRes :: [Expr] -> Bool
addRes [f, (Lit (LitDouble x))] = f `eqIgT` add && x > 0

subRes :: [Expr] -> Bool
subRes [f, (Lit (LitDouble x))] = f `eqIgT` sub && x < 0

approxSqrtRes :: [Expr] -> Bool
approxSqrtRes [f, (Lit (LitDouble x))] = f `eqIgT` approxSqrt && x > 0

pythagoreanRes :: [Expr] -> Bool
pythagoreanRes [f, (Lit (LitDouble x))] = f `eqIgT` pythagorean && x /= 0

functionSatisfiesRes :: [Expr] -> Bool
functionSatisfiesRes (Var (Id (Name "notNegativeAt0" _ _) _):Var (Id (Name"add1" _ _) _):ex) = True
functionSatisfiesRes _ = False
