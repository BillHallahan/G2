module HigherOrderMathTest where

import G2.Internals.Core.Language

abs2 = Var "abs2" (TyFun (TyConApp "Double" []) (TyConApp "Double" []))
square = Var "square" (TyFun (TyConApp "Double" []) (TyConApp "Double" []))
fourthPower = Var "fourthPower" (TyFun (TyConApp "Double" []) (TyConApp "Double" []))

isPositiveAt0 = Var "isPositiveAt0" (TyFun (TyFun (TyConApp "Double" []) (TyConApp "Double" [])) (TyConApp "Bool" []))

abs2NonNeg :: [Expr] -> Bool
abs2NonNeg [f, (Const (CDouble x))] = f == abs2 && x >= 0
abs2NonNeg _ = False

abs2Neg :: [Expr] -> Bool
abs2Neg [f, (Const (CDouble x))] = f == abs2 && x < 0
abs2Neg _ = False

squareRes :: [Expr] -> Bool
squareRes [f, (Const (CDouble x))] = f == square && (x == 0 || x == 1)
squareRes _ = False

fourthPowerRes :: [Expr] -> Bool
fourthPowerRes [f, (Const (CDouble x))] = f == square && (x == 0 || x == 1)
fourthPowerRes _ = False

functionSatisfiesRes :: [Expr] -> Bool
functionSatisfiesRes (Var "isPositiveAt0" _:Var "add1" _:ex) = True
functionSatisfiesRes _ = False
