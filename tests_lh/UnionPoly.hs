{-# LANGUAGE OverloadedStrings #-}

module UnionPoly (unionPolyTests) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.TyVarEnv as TV
import G2.Liquid.Inference.UnionPoly

import qualified Data.Text as T

import Test.Tasty
import Test.Tasty.HUnit

unionPolyTests :: TestTree
unionPolyTests =
    testGroup "UnionPoly"
    [
      testCase "Let unification" $ assertBool "Polymorphic unification failed with lets" letTest
    , testCase "Lambda unification 1" $ assertBool "Polymorphic unification failed with lambdas" lambdaTest1
    , testCase "Lambda unification 2" $ assertBool "Polymorphic unification failed with lambdas" lambdaTest2
    ]

letTest :: Bool
letTest =
    let
        f = defName "f"
        g = defName "g"
        eenv = letExprEnv f g
        
        ut = sharedTyConsEE TV.empty [f, g] eenv
    in
    case lookupUT g ut of
        Just (TyFun t1@(TyVar _) t2) -> t1 == t2 
        _ -> False

letExprEnv :: Name -> Name -> ExprEnv
letExprEnv f g =
    let
        call = defName "call"
        a = defName "a"

        a_id = Id a TYPE
        a_ty = TyVar a_id

        int = defName "Int"
        int_ty = TyCon int TYPE

        g_id = Id g (TyFun int_ty int_ty)
        r_id = Id (defName "r") (TyFun int_ty int_ty)
        call_id = Id call . TyForAll a_id $ TyFun (TyFun a_ty a_ty) a_ty

        f_e = Let [(r_id, Var g_id)] . App (App (Var call_id) (Type int_ty)) $ Var r_id

        x_id = Id (defName "x") int_ty
        y_id = Id (defName "y") int_ty
        g_e = Lam TermL x_id (Var y_id)
    in
    E.fromList [(f, f_e), (g, g_e)]

lambdaTest1 :: Bool
lambdaTest1 =
    let
        f = defName "f"
        g = defName "g"
        h = defName "h"
        eenv = lambdaExprEnv1 f g h

        ut = sharedTyConsEE TV.empty [f, g, h] eenv
    in
    case lookupUT h ut of
        Just (TyFun t1@(TyVar _) t2) -> t1 == t2 
        _ -> False

lambdaExprEnv1 :: Name -> Name -> Name -> ExprEnv
lambdaExprEnv1 f g h =
    let
        a = defName "a"
        a_id = Id a TYPE
        a_ty = TyVar a_id

        int = defName "Int"
        int_ty = TyCon int TYPE

        g_id = Id g . TyForAll a_id $ TyFun (TyFun a_ty a_ty) a_ty
        h_id = Id h $ TyFun int_ty int_ty

        j_id = Id (defName "j") (TyFun a_ty a_ty)
        x_id = Id (defName "x") int_ty

        g_e = Lam TypeL a_id . Lam TermL j_id $ App (App (Var g_id) (Type a_ty)) (Var j_id)
        h_e = Lam TermL x_id $ Var x_id
        f_e = App (App (Var g_id) (Type int_ty)) . Lam TermL x_id $ App (Var h_id) (Var x_id)
    in
    E.fromList [(f, f_e), (g, g_e), (h, h_e)]

lambdaTest2 :: Bool
lambdaTest2 =
    let
        f = defName "f"
        g = defName "g"
        h = defName "h"
        eenv = lambdaExprEnv2 f g h

        ut = sharedTyConsEE TV.empty [f, g, h] eenv
    in
    case lookupUT h ut of
        Just (TyFun t1@(TyVar _) t2) -> t1 == t2 
        _ -> False

lambdaExprEnv2 :: Name -> Name -> Name -> ExprEnv
lambdaExprEnv2 f g h =
    let
        a = defName "a"
        a_id = Id a TYPE
        a_ty = TyVar a_id

        int = defName "Int"
        int_ty = TyCon int TYPE

        g_id = Id g . TyForAll a_id . TyFun (TyFun int_ty int_ty) $ TyFun (TyFun a_ty a_ty) a_ty
        h_id = Id h $ TyFun int_ty int_ty

        j_id = Id (defName "j") (TyFun int_ty int_ty)
        k_id = Id (defName "k") (TyFun a_ty a_ty)
        x_id = Id (defName "x") int_ty
        y_id = Id (defName "y") a_ty

        bind_id = Id (defName "bind") (TyForAll a_id (TyFun a_ty a_ty))

        g_e = Lam TypeL a_id
            . Lam TermL j_id
            . Lam TermL k_id $ App (App (App (Var g_id) (Type a_ty)) (Var j_id)) (Var k_id)
        h_e = Lam TermL x_id $ Var x_id
        f_e = Let [(bind_id, Lam TypeL a_id $ Lam TermL y_id (Var y_id))]
            . App (App (App (Var g_id) (Type int_ty)) (App (Var bind_id) (Type int_ty))) $ Var h_id
    in
    E.fromList [(f, f_e), (g, g_e), (h, h_e)]

defName :: T.Text -> Name
defName n = Name n Nothing 0 Nothing