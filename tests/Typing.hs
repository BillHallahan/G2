{-# LANGUAGE OverloadedStrings #-}

module Typing (typingTests) where

import Prelude hiding (either, maybe)

import G2.Internals.Language

import Test.Tasty
import Test.Tasty.HUnit

typingTests :: IO TestTree
typingTests = return typingTests'

typingTests' :: TestTree
typingTests' =
    testGroup "Typing"
    [
      testCase "Function application" $ assertBool "Function application failed" test1
    , testCase "Polymorphic DataCon application" $ assertBool "Polymorphic DataCon application failed" test2
    , testCase "Polymorphic Function application" $ assertBool "Polymorphic Function application failed" test3
    , testCase "Polymorphic Function application 2" $ assertBool "Polymorphic Function application 2 failed" test4
    , testCase "Polymorphic Function application 3" $ assertBool "Polymorphic Function application 3 failed" funcAppTest
    , testCase "Polymorphic Function" $ assertBool "Polymorphic Function failed" funcTest
    , testCase "Kind application" $ assertBool "Kind application failed" tyAppKindTest
    ]

test1 :: Bool
test1 = typeOf (App f1 x1) == int

test2 :: Bool
test2 = typeOf (App (App just (Type int)) x1) == TyApp maybe int

test3 :: Bool
test3 = typeOf 
        (App 
            (App
                f2 
                (Type int)
            )
            x1
        )
        ==
        int

test4 :: Bool
test4 = typeOf
        (App 
            (App
                (App
                    f3
                    (Type int)
                )
                (Type float)
            )
            x1
        )
        ==
        float

funcAppTest :: Bool
funcAppTest = typeOf (App (App idDef (Type int)) x1) == int

funcTest :: Bool
funcTest = idDef .:: (TyForAll (NamedTyBndr aid) (TyFun a a))

tyAppKindTest :: Bool
tyAppKindTest = typeOf (TyApp either a) == TyFun TYPE TYPE

-- Typed Expr's
x1 :: Expr
x1 = Var $ Id (Name "x1" Nothing 0 Nothing) int

f1 :: Expr
f1 = Var $ Id (Name "f1" Nothing 0 Nothing) (TyFun int int)

f2 :: Expr
f2 = Var $ Id (Name "f2" Nothing 0 Nothing)
                (TyForAll
                    (NamedTyBndr bid)
                    (TyFun b b)
                )

f3 :: Expr
f3 = Var $ Id (Name "f3" Nothing 0 Nothing)
                (TyForAll
                    (NamedTyBndr bid)
                    (TyForAll
                        (NamedTyBndr aid)
                        (TyFun b a)
                    )
                )

just :: Expr
just = Data $ DataCon 
                    (Name "Just" Nothing 0 Nothing) 
                    (TyForAll 
                        (NamedTyBndr aid) 
                        (TyFun a (TyApp maybe a))
                    )

idDef :: Expr
idDef = Lam TypeL aid 
            (Lam TermL
                (Id (Name "x" Nothing 0 Nothing) a)
                (Var (Id (Name "x" Nothing 0 Nothing) a))
            )

-- Types
int :: Type
int = TyConApp (Name "Int" Nothing 0 Nothing) TYPE

float :: Type
float = TyConApp (Name "Float" Nothing 0 Nothing) TYPE

maybe :: Type
maybe = TyConApp (Name "Maybe" Nothing 0 Nothing) (TyFun TYPE TYPE)

either :: Type
either = TyConApp (Name "Either" Nothing 0 Nothing) (TyFun TYPE (TyFun TYPE TYPE))

a :: Type
a = TyVar aid

aid :: Id
aid = Id (Name "a" Nothing 0 Nothing) TYPE

b :: Type
b = TyVar bid

bid :: Id
bid = Id (Name "b" Nothing 0 Nothing) TYPE