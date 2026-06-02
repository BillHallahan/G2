{-# LANGUAGE OverloadedStrings #-}

module Expr (exprTests) where

import G2.Execution.NewPC
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.TyVarEnv as TV 

import qualified Data.Text as T

import Test.Tasty
import Test.Tasty.HUnit

exprTests :: TestTree
exprTests =
    testGroup "Expr"
    [ testCase "Eta Expand To" $ assertBool "Eta Expand To failed" etaExpandTo1
    , testCase "Eta Expand To" $ assertBool "Eta Expand To failed" etaExpandTo2
    , testCase "Eta Expand To" $ assertBool "Eta Expand To failed" etaExpandTo3
    , testCase "Eta Expand To" $ assertBool "Eta Expand To failed" etaExpandTo4
    , testCase "Eta Expand To" $ assertBool "Eta Expand To failed" etaExpandToOverSat1
    
    , testCase "Indistinguishable 1" $ assertBool "indistinguishableRegions failed" indistinguishable1
    , testCase "Indistinguishable 2" $ assertBool "indistinguishableRegions failed" indistinguishable2
    , testCase "Indistinguishable 3" $ assertBool "indistinguishableRegions failed" indistinguishable3
    , testCase "Indistinguishable 4" $ assertBool "indistinguishableRegions failed" indistinguishable4
    , testCase "Indistinguishable 5" $ assertBool "indistinguishableRegions failed" indistinguishable5
    , testCase "Indistinguishable 6" $ assertBool "indistinguishableRegions failed" indistinguishable6
    , testCase "Indistinguishable 7" $ assertBool "indistinguishableRegions failed" indistinguishable7 ]

etaExpandTo1 :: Bool
etaExpandTo1 =
    let
        (e, _) = etaExpandTo TV.empty eenv (mkNameGen ()) 1 idF
    in
    case e of
        (Lam TermL i (App _ (Var i'))) -> i == i'
        _ -> False

etaExpandTo2 :: Bool
etaExpandTo2 =
    let
        (e, _) = etaExpandTo TV.empty eenv (mkNameGen ()) 1 (Var (Id undefinedN (TyFun int int)))
    in
    case e of
        Var (Id n (TyFun _ _)) -> n == undefinedN
        _ -> False

etaExpandTo3 :: Bool
etaExpandTo3 =
    let
        (e, _) = etaExpandTo TV.empty eenv (mkNameGen ()) 1
                (Let [(fId, (Var (Id idN (TyFun int int))))] (Var fId))
    in
    case e of
       (Lam TermL i (App (Let _ _) (Var i'))) -> i == i'
       _ -> False

etaExpandTo4 :: Bool
etaExpandTo4 =
    let
        (e, _) = etaExpandTo TV.empty eenv (mkNameGen ()) 1
                (Let [(fId, (Var (Id undefinedN (TyFun int int))))] (Var fId))
    in
    case e of
       Let [(i, _)] (Var i') -> i == fId && i' == fId
       _ -> False

etaExpandToOverSat1 :: Bool
etaExpandToOverSat1 =
    let
        (e, _) = etaExpandTo TV.empty eenv (mkNameGen ()) 3 idF
    in
    case e of
        (Lam TermL i (App _ (Var i'))) -> i == i'
        _ -> False

-- DataCons
intD :: DataCon
intD = DataCon (Name "Int" Nothing 0 Nothing) int [] []

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

-- Testing indistinguishability
indistinguishable1 :: Bool
indistinguishable1 = indistinguishableRegions E.empty e1 e2 == Just e3
    where
        e1 = App
                (Data dc1)
                (App
                    (Data dc1)
                    (App 
                        (Lam TermL (Id bN TyUnknown) (Lit $ LitInt 1))
                        (Var (Id idN TyUnknown))
                    )
                )

        e2 = App
                (Data dc1)
                (App
                    (Data dc1)
                    (Lit $ LitInt 5)
                )

        e3 = App
                (Data dc1)
                (App
                    (Data dc1)
                    (Prim Undefined TyBottom)
                )

        dc1 = mkDC "DC1"

indistinguishable2 :: Bool
indistinguishable2 = indistinguishableRegions E.empty e1 e2 == Just e3
    where
        e1 = App
                (App (Data dc1) (Type (TyCon n1 TYPE)))
                (App
                    (App (Data dc1) (Type (TyCon n1 TYPE)))
                    (App 
                        (Lam TermL (Id bN TyUnknown) (Lit $ LitInt 1))
                        (Var (Id idN TyUnknown))
                    )
                )

        e2 = App
                (App (Data dc1) (Type (TyCon n1 TYPE)))
                (App
                    (App (Data dc1) (Type (TyCon n1 TYPE)))
                    (Lit $ LitInt 5)
                )

        e3 = App
                (App (Data dc1) (Type (TyCon n1 TYPE)))
                (App 
                    (App (Data dc1) (Type (TyCon n1 TYPE)))
                    (Prim Undefined TyBottom)
                )

        n1 = Name "n1" Nothing 0 Nothing
        dc1 = mkDC "DC1"

indistinguishable3 :: Bool
indistinguishable3 = indistinguishableRegions E.empty e1 e2 == Nothing
    where
        e1 = App
                (App (Data dc1) (Type (TyCon n1 TYPE)))
                (App
                    (App (Data dc1) (Type (TyCon n1 TYPE)))
                    (App 
                        (Lam TermL (Id bN TyUnknown) (Lit $ LitInt 1))
                        (Var (Id idN TyUnknown))
                    )
                )

        e2 = App
                (App (Data dc1) (Type (TyCon n2 TYPE)))
                (App
                    (App (Data dc1) (Type (TyCon n1 TYPE)))
                    (App 
                        (Lam TermL (Id bN TyUnknown) (Lit $ LitInt 1))
                        (Var (Id idN TyUnknown))
                    )
                )

        n1 = Name "n1" Nothing 0 Nothing
        n2 = Name "n2" Nothing 0 Nothing
        dc1 = mkDC "DC1"

indistinguishable4 :: Bool
indistinguishable4 = indistinguishableRegions E.empty e1 e2 == Nothing
    where
        e1 = App
                (App (Data dc1) (Type (TyCon n1 TYPE)))
                (App
                    (App (Data dc1) (Type (TyCon n1 TYPE)))
                    (App 
                        (Lam TermL (Id bN TyUnknown) (Lit $ LitInt 1))
                        (Var (Id idN TyUnknown))
                    )
                )

        e2 = App
                (App (Data dc1) (Type (TyCon n1 TYPE)))
                (App
                    (App (Data dc2) (Type (TyCon n1 TYPE)))
                    (App 
                        (Lam TermL (Id bN TyUnknown) (Lit $ LitInt 1))
                        (Var (Id idN TyUnknown))
                    )
                )

        n1 = Name "n1" Nothing 0 Nothing
        dc1 = mkDC "DC1"
        dc2 = mkDC "DC2"

indistinguishable5 :: Bool
indistinguishable5 = indistinguishableRegions E.empty e e == Just e
    where
        e = (App (Data dc1) (Lit (LitInt 2)))
        dc1 = mkDC "DC1"

indistinguishable6 :: Bool
indistinguishable6 = indistinguishableRegions E.empty e1 e2 == Just (App (Data dc1) (Prim Undefined TyBottom))
    where
        e1 = (App (Data dc1) (Lit (LitInt 2)))
        e2 = (App (Data dc1) (App undefined undefined))
        dc1 = mkDC "DC1"

indistinguishable7 :: Bool
indistinguishable7 = indistinguishableRegions E.empty e1 e2 == Nothing
    where
        e1 = (App (Data dc1) (Lit (LitInt 1)))
        e2 = (App (Data dc1) (Lit (LitInt 2)))
        dc1 = mkDC "DC1"


mkDC :: T.Text -> DataCon
mkDC s = DataCon { dc_name = Name s Nothing 0 Nothing, dc_type = TyUnknown, dc_univ_tyvars = [], dc_exist_tyvars = []}