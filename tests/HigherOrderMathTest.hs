module HigherOrderMathTest where

import G2.Internals.Core.Language

abs2 = Var "abs2" (TyFun (TyConApp "Double" []) (TyConApp "Double" []))
square = Var "square" (TyFun (TyConApp "Double" []) (TyConApp "Double" []))
negativeSquare = Var "negativeSquare" (TyFun (TyConApp "Double" []) (TyConApp "Double" []))
fourthPower = Var "fourthPower" (TyFun (TyConApp "Double" []) (TyConApp "Double" []))
add1 = Var "add1" (TyFun (TyConApp "Double" []) (TyConApp "Double" []))
sub1 = Var "sub1" (TyFun (TyConApp "Double" []) (TyConApp "Double" []))

add = Var "add" (TyFun (TyConApp "Double" []) (TyFun (TyConApp "Double" []) (TyConApp "Double" [])))
sub = Var "sub" (TyFun (TyConApp "Double" []) (TyFun (TyConApp "Double" []) (TyConApp "Double" [])))

notNegativeAt0 = Var "notNegativeAt0" (TyFun (TyFun (TyConApp "Double" []) (TyConApp "Double" [])) (TyConApp "Bool" []))
notNegativeAt0NegativeAt1 = Var "notNegativeAt0NegativeAt1" (TyFun (TyFun (TyConApp "Double" []) (TyConApp "Double" [])) (TyConApp "Bool" []))

abs2NonNeg :: [Expr] -> Bool
abs2NonNeg [f, (Const (CDouble x))] = f == abs2 && x >= 0
abs2NonNeg _ = False

abs2Neg :: [Expr] -> Bool
abs2Neg [f, (Const (CDouble x))] = f == abs2 && x < 0
abs2Neg _ = False

squareRes :: [Expr] -> Bool
squareRes [f, (Const (CDouble x))] = f == square && (x == 0 || x == 1)
squareRes _ = False

negativeSquareRes :: [Expr] -> Bool
negativeSquareRes [f] = f == negativeSquare
negativeSquareRes _ = False

fourthPowerRes :: [Expr] -> Bool
fourthPowerRes [f, (Const (CDouble x))] = f == square && (x == 0 || x == 1)
fourthPowerRes _ = False

addRes :: [Expr] -> Bool
addRes [f, (Const (CDouble x))] = f == add && x > 0

subRes :: [Expr] -> Bool
subRes [f, (Const (CDouble x))] = f == sub && x < 0

functionSatisfiesRes :: [Expr] -> Bool
functionSatisfiesRes (Var "notNegativeAt0" _:Var "add1" _:ex) = True
functionSatisfiesRes _ = False
