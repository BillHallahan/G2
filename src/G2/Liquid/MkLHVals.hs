{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.MkLHVals (mkLHVals) where

import G2.Language as Lang
import G2.Language.KnownValues
import qualified G2.Language.ExprEnv as E

import qualified Data.HashSet as S
import qualified Data.Text as T
import qualified G2.Language.TyVarEnv as TV 

mkLHVals :: State t
         -> S.HashSet Name
         -> [Name]
         -> NameGen
         -> (ExprEnv, KnownValues, TypeClasses, S.HashSet Name, [Name], NameGen)
mkLHVals (State { expr_env = eenv
                , type_env = tenv
                , known_values = kv
                , type_classes = tc 
                , tyvar_env = tvnv }) inst exported ng =
    let
        renme = E.keys eenv
        ((meenv, mkv, mtc, minst, mexported), ng') = doRenames renme ng (eenv, kv, tc, inst, exported)

        (newMod, meenv', ng'') = symGenIfZero tvnv (modFunc mkv) meenv tenv mkv mtc ng'
    in
    (meenv', mkv { modFunc = newMod } , mtc, minst, mexported, ng'')

symGenIfZero :: TV.TyVarEnv -> Name -> ExprEnv -> TypeEnv -> KnownValues -> TypeClasses -> NameGen -> (Name, ExprEnv, NameGen)
symGenIfZero tv n eenv tenv kv tc ng =
    case E.lookup n eenv of
        Just e ->
            let
                (newN, ng') = freshSeededString ("symGen" `T.append` nameOcc n) ng
                (e', ng'') = symGenIfZero' tv e eenv tenv kv tc ng'
            in
            (newN, E.insert newN e' eenv, ng'')
        Nothing -> error "symGenIfZero: Name not found"

symGenIfZero' :: TV.TyVarEnv -> Expr -> ExprEnv -> TypeEnv -> KnownValues -> TypeClasses -> NameGen -> (Expr, NameGen)
symGenIfZero' tv e eenv tenv kv tc ng =
    let
        (ars, ng') = argTyToLamUseIds (spArgumentTypes $ typeOf tv e) ng

        class_ty = case ars of
                    (TypeL, c_ty):_ -> c_ty
                    _ -> error "symGenIfZero: Type not found"
        snd_int = haveType tv (TyVar class_ty) (map snd ars) !! 1

        int_tcs_m = tcWithNameMap tv (integralTC kv) (map snd ars)
        int_tc = case typeClassInst tc int_tcs_m (integralTC kv) (TyVar class_ty) of
                        Just int_tc' -> int_tc'
                        Nothing -> error "symGenIfZero: Typeclass dictionary not found"

        type_expr =  Type (TyVar class_ty)
        num_dict = App 
                    (App
                        (mkRealExtractNum kv)
                        type_expr
                    )
                    (App 
                        (App
                            (mkIntegralExtactReal kv)
                            type_expr
                        )
                        int_tc
                    )
        eq_dict =
                App
                    (App
                        (mkOrdExtractEq kv)
                        type_expr
                    )
                    (App 
                        (App
                            (mkRealExtractOrd kv)
                            type_expr
                        )
                        (App 
                            (App
                                (mkIntegralExtactReal kv)
                                type_expr
                            )
                            int_tc
                        )
                    )
        zero = App (mkDCInteger kv tenv) (Lit (LitInt 0))
        zero_con = mkApp [mkFromInteger kv eenv, type_expr, num_dict, zero]
        eq = mkApp [ Var (Id (eqFunc kv) TyUnknown)
                   , type_expr
                   , eq_dict
                   , Var snd_int
                   , zero_con]

        (i, ng'') = freshId (Lang.tyBool kv) ng'

        trueDC = mkDCTrue kv tenv

        ret_t = returnType (typeOf tv e)

        e' = mkLams ars
                $ Case eq i ret_t
                    [ Alt Default (mkApp (e:map (Var . snd) ars))
                    , Alt (DataAlt trueDC []) (SymGen SNoLog ret_t)]
    in
    (e', ng'')

haveType :: TV.TyVarEnv -> Type -> [Id] -> [Id]
haveType tv t = filter (\e -> typeOf tv e == t)

argTyToLamUseIds :: [ArgType] -> NameGen -> ([(LamUse, Id)], NameGen)
argTyToLamUseIds =
    mapNG (\ar_ty ng ->
                case ar_ty of
                        NamedType i -> ((TypeL, i), ng)
                        AnonType t ->
                            let
                                (n, ng') = freshName ng
                            in
                            ((TermL, Id n t), ng'))
