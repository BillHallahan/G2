{-# LANGUAGE FlexibleContexts #-}

module UnitTests where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Map as M
import qualified Data.Monoid as Mon

import G2.Internals.Core.Language
import G2.Internals.Core.ASTHandler

unitTests :: IO TestTree
unitTests =
    return . testGroup "Unit" $
        [ testCase "removeLams" (expr4NoLams @=? removeLams expr4)
        , testCase "removeLamsFixed" (expr4NoLams @=? removeLamsFixed expr4)
        , testCase "concatNames" (expr4Concatted @=? concatNames expr4)
        , testCase "countExpr1" (1 @=? countExpr expr1)
        , testCase "countExpr2" (4 @=? countExpr expr2)
        , testCase "countExpr3" (11 @=? countExpr expr3)
        , testCase "countExprMap" (16 @=? countExpr exprMap)
        , testCase "countType1" (1 @=? countType expr1)
        , testCase "countType2" (7 @=? countType expr2)
        , testCase "countType3" (16 @=? countType expr3)
        , testCase "countTypeMap" (24 @=? countType exprMap)]

-- Returns the given expression container, but with all lambdas removed
-- (note: bounding is not performed.  The point is to test modify, not
-- to perform an actually useful operation.)
removeLams :: (ASTContainer t Expr) => t -> t
removeLams = modifyContainer removeLams'
    where
        removeLams' :: Expr -> Expr
        -- removeLams' recursively removes all Lams from the beginning of the expression
        -- this is need to remove ALL Lams from the original expression
        -- without this recursive call Lam(Lam e t) t' would become Lam (removeLams e) t
        -- not (removeLams e)
        removeLams' (Lam _ e _) = removeLams' e
        removeLams' e = e

-- The same as removeLams, but by using modifyContainerFix, we avoid having to write
-- removeLams' recursively
removeLamsFixed :: (ASTContainer t Expr) => t -> t
removeLamsFixed = modifyContainerFix removeLams'
    where
        removeLams' :: Expr -> Expr
        removeLams' (Lam _ e _) = e
        removeLams' e = e

concatNames :: (ASTContainer t Expr) => t -> t
concatNames = modifyContainerM concatNames'
    where
        concatNames' :: [Name] -> Expr -> (Expr, [Name])
        concatNames' ns (Var n t) =
            let n' = (mconcat ns) ++ n in (Var n' t, [n])
        concatNames' ns (Lam n e t) =
            let n' = (mconcat ns) ++ n in (Lam n' e t, [n])
        concatNames' _ e = (e, [])

-- Counts the number of expressions that are nested in a given expression container
countExpr :: (ASTContainer t Expr) => t -> Int
countExpr = Mon.getSum . evalContainerASTs (countExpr')
    where
        countExpr' :: Expr -> Mon.Sum Int
        countExpr' _ = Mon.Sum 1

-- Counts the number of types that are nested in a given type container
countType :: (ASTContainer t Type) => t -> Int
countType = Mon.getSum . evalContainerASTs (countType')
    where
        countType' :: Type -> Mon.Sum Int
        countType' _ = Mon.Sum 1

expr1 = Var "a" (TyConApp "Int" [])

expr2 = Lam "a" 
            (App
                (Var "f" (TyFun (TyConApp "Int" []) (TyConApp "Bool" [])))
                (Var "a" (TyConApp "Int" []))) (TyFun (TyConApp "Int" []) (TyConApp "Bool" []))

expr3 = Case (Var "n" (TyConApp "X" []))
            [ (Alt (DataCon "Y" (-1) (TyConApp "X" []) [], ["x1"]),
                    App
                        (Var "f" (TyFun (TyConApp "Int" []) (TyConApp "Bool" [])))
                        (Var "x1" (TyConApp "Int" [])))
             , (Alt (DataCon "Z" (-1) (TyConApp "X" []) [], ["x1"]),
                    App
                        (App
                            (Var "g" (TyFun (TyConApp "Int" []) (TyFun (TyConApp "Int" []) (TyConApp "Bool" []))))
                            (Var "x1" (TyConApp "Int" [])))
                    (Var "x1" (TyConApp "Int" [])))
             , (Alt (DEFAULT, ["d"]), Var "False" (TyConApp "Bool" []))
            ]
            (TyConApp "Bool" [])

expr4 =
    Lam "g"
        (Lam "n"
            (App
                (Lam "x" (Lam "y" (Var "m" (TyConApp "X" [])) (TyConApp "X" [])) (TyConApp "X" []))
                (Lam "x" (Var "n" (TyConApp "X" [])) (TyConApp "X" []))
            )
         (TyConApp "X" [])
        )
    (TyConApp "X" [])

expr4NoLams = (App
                (Var "m" (TyConApp "X" []))
                (Var "n" (TyConApp "X" []))
              )

expr4Concatted =
    Lam "g"
        (Lam "gn"
            (App
                (Lam "gnx" (Lam "gnxy" (Var "gnxym" (TyConApp "X" [])) (TyConApp "X" [])) (TyConApp "X" []))
                (Lam "gnx" (Var "gnxn" (TyConApp "X" [])) (TyConApp "X" []))
            )
         (TyConApp "X" [])
        )
    (TyConApp "X" [])

exprMap = M.fromList [("expr1", expr1), ("expr2", expr2), ("expr3", expr3)]
