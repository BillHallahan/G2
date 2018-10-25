{-# LANGUAGE OverloadedStrings #-}

module Expr (exprTests) where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E

import Test.Tasty
import Test.Tasty.HUnit

exprTests :: IO TestTree
exprTests = return exprTests'

exprTests' :: TestTree
exprTests' =
    testGroup "Expr"
    [ testCase "Eta Expand To" $ assertBool "Eta Expand To failed" etaExpandTo1
    , testCase "Eta Expand To" $ assertBool "Eta Expand To failed" etaExpandTo2
    , testCase "Eta Expand To" $ assertBool "Eta Expand To failed" etaExpandTo3
    , testCase "Eta Expand To" $ assertBool "Eta Expand To failed" etaExpandTo4
    , testCase "Eta Expand To" $ assertBool "Eta Expand To failed" etaExpandToOverSat1 ]

etaExpandTo1 :: Bool
etaExpandTo1 =
    let
        (e, _) = etaExpandTo eenv (mkNameGen ()) 1 idF
    in
    case e of
        (Lam TermL i (App _ (Var i'))) -> i == i'
        _ -> False

etaExpandTo2 :: Bool
etaExpandTo2 =
    let
        (e, _) = etaExpandTo eenv (mkNameGen ()) 1 (Var (Id undefinedN (TyFun int int)))
    in
    case e of
        Var (Id n (TyFun _ _)) -> n == undefinedN
        _ -> False

etaExpandTo3 :: Bool
etaExpandTo3 =
    let
        (e, _) = etaExpandTo eenv (mkNameGen ()) 1
                (Let [(fId, (Var (Id idN (TyFun int int))))] (Var fId))
    in
    case e of
       (Lam TermL i (App (Let _ _) (Var i'))) -> i == i'
       _ -> False

etaExpandTo4 :: Bool
etaExpandTo4 =
    let
        (e, _) = etaExpandTo eenv (mkNameGen ()) 1
                (Let [(fId, (Var (Id undefinedN (TyFun int int))))] (Var fId))
    in
    case e of
       Let [(i, _)] (Var i') -> i == fId && i' == fId
       _ -> False

etaExpandToOverSat1 :: Bool
etaExpandToOverSat1 =
    let
        (e, _) = etaExpandTo eenv (mkNameGen ()) 3 idF
    in
    case e of
        (Lam TermL i (App _ (Var i'))) -> i == i'
        _ -> False

-- DataCons
intD :: DataCon
intD = DataCon (Name "Int" Nothing 0 Nothing) int

-- Types
int :: Type
int = TyCon (Name "Int" Nothing 0 Nothing) TYPE

-- Typed Expr's
x1N :: Name
x1N = Name "x1" Nothing 0 Nothing

fId :: Id
fId = Id (Name "f" Nothing 0 Nothing) (TyFun int int)

idN :: Name
idN = Name "id" Nothing 0 Nothing

idF :: Expr
idF = Var $ Id idN (TyFun int int)

bN :: Name
bN = Name "b" Nothing 0 Nothing

undefinedN :: Name
undefinedN = Name "undefined" Nothing 0 Nothing

eenv :: ExprEnv
eenv = E.fromList [ (x1N, App (Data intD) (Lit (LitInt 1))) 
                  , (idN, Lam TermL (Id bN int) (Var (Id bN int)))
                  , (undefinedN, Prim Undefined TyBottom) ]