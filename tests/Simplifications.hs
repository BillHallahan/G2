{-# LANGUAGE OverloadedStrings #-}

module Simplifications (simplificationTests) where

import G2.Language.Simplification
import G2.Language.Syntax

import Test.Tasty
import Test.Tasty.HUnit

simplificationTests :: TestTree
simplificationTests =
    testGroup "Simplifications" [
          testCase "AppLamSimplification" (assertBool "Substituting two variables" simplifyAppLambdasTest1)
        , testCase "AppLamSimplification" (assertBool "Substituting two variables" simplifyAppLambdasTest2)
        ]


simplifyAppLambdasTest1 :: Bool
simplifyAppLambdasTest1 =
    let
        le = Lam TermL id1 
                . Lam TermL id2
                $ App (Var id1) (Var id2)
        e = App (App le (Var id3)) (Var id4)
    in
    simplifyAppLambdas e == App (Var id3) (Var id4)


simplifyAppLambdasTest2 :: Bool
simplifyAppLambdasTest2 =
    let
        le = Lam TermL id1 
                $ (App (Lam TermL id2 (Var id2)) (Var id1))
        e = App le (Var id3)
    in
    simplifyAppLambdas e == Var id3

id1 :: Id
id1 = Id (Name "a" Nothing 0 Nothing) TyUnknown

id2 :: Id
id2 = Id (Name "b" Nothing 0 Nothing) TyUnknown

id3 :: Id
id3 = Id (Name "c" Nothing 0 Nothing) TyUnknown

id4 :: Id
id4 = Id (Name "d" Nothing 0 Nothing) TyUnknown
