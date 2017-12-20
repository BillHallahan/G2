module HigherOrderMathTest where

import G2.Internals.Language

import TestUtils

abs2 :: Expr
abs2 = Var (Id (Name "abs2" (Just "HigherOrderMath") 0) tyBoolS)

abs3 :: Expr
abs3 = Var (Id (Name "abs3" (Just "HigherOrderMath") 0) tyBoolS)

square :: Expr
square = Var (Id (Name "square" (Just "HigherOrderMath") 0) tyBoolS)

negativeSquare :: Expr
negativeSquare = Var (Id (Name "negativeSquare" (Just "HigherOrderMath") 0) tyBoolS)

fourthPower :: Expr
fourthPower = Var (Id (Name "fourthPower" (Just "HigherOrderMath") 0) tyBoolS)

add1 :: Expr
add1 = Var (Id (Name "add1" (Just "HigherOrderMath") 0) tyBoolS)

sub1 :: Expr
sub1 = Var (Id (Name "sub1" (Just "HigherOrderMath") 0) tyBoolS)

add :: Expr
add = Var (Id (Name "add" (Just "HigherOrderMath") 0) tyBoolS)

sub :: Expr
sub = Var (Id (Name "sub" (Just "HigherOrderMath") 0) tyBoolS)

approxSqrt :: Expr
approxSqrt = Var (Id (Name "approxSqrt" (Just "HigherOrderMath") 0) tyBoolS)

pythagorean :: Expr
pythagorean = Var (Id (Name "pythagorean" (Just "HigherOrderMath") 0) tyBoolS)

notNegativeAt0 :: Expr
notNegativeAt0 = Var (Id (Name "notNegativeAt0" (Just "HigherOrderMath") 0) TyBottom)

notNegativeAt0NegativeAt1 :: Expr
notNegativeAt0NegativeAt1 = Var (Id (Name "notNegativeAt0NegativeAt1" (Just "HigherOrderMath") 0) TyBottom)

abs2NonNeg :: [Expr] -> Bool
abs2NonNeg [f, App _ (Lit (LitDouble x))] = f `eqIgT` abs2 && x >= 0
abs2NonNeg _ = False

allabs2NonNeg :: [Expr] -> Bool
allabs2NonNeg [f, App _ (Lit (LitDouble x))] = not (f `eqIgT` abs3) || x >= 0
allabs2NonNeg _ = True

squareRes :: [Expr] -> Bool
squareRes [f, App _ (Lit (LitDouble x))] = f `eqIgT` square && (x == 0 || x == 1)
squareRes _ = False

negativeSquareRes :: [Expr] -> Bool
negativeSquareRes [f] = f `eqIgT` negativeSquare
negativeSquareRes _ = False

fourthPowerRes :: [Expr] -> Bool
fourthPowerRes [f, App _ (Lit (LitDouble x))] = f `eqIgT` square && (x == 0 || x == 1)
fourthPowerRes _ = False

addRes :: [Expr] -> Bool
addRes [f, App _ (Lit (LitDouble x))] = f `eqIgT` add && x > 0
addRes _ = False

subRes :: [Expr] -> Bool
subRes [f, App _ (Lit (LitDouble x))] = f `eqIgT` sub && x < 0
subRes _ = False

approxSqrtRes :: [Expr] -> Bool
approxSqrtRes [f, App _ (Lit (LitDouble x))] = f `eqIgT` approxSqrt && x > 0
approxSqrtRes _ = False

pythagoreanRes :: [Expr] -> Bool
pythagoreanRes [f, App _ (Lit (LitDouble x))] = f `eqIgT` pythagorean && x /= 0
pythagoreanRes _ = False

functionSatisfiesRes :: [Expr] -> Bool
functionSatisfiesRes (Var (Id (Name "notNegativeAt0" _ _) _):Var (Id (Name"add1" _ _) _):_) = True
functionSatisfiesRes _ = False

tyBoolS :: Type
tyBoolS = TyConApp (Name "Bool" Nothing 0) []