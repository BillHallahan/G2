{-# LANGUAGE OverloadedStrings #-}

-- This module generates functions in the expr_env that walk over the whole structure of an ADT.
-- This forces evaluation of the ADT
module G2.Internals.Initialization.DeepSeqWalks (createDeepSeqWalks) where

import G2.Internals.Language

import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

type BoundName = Name

createDeepSeqWalks :: ExprEnv -> TypeEnv -> NameGen -> (ExprEnv, NameGen, Walkers)
createDeepSeqWalks eenv tenv ng =
    let
        tenv' = M.toList tenv
    in
    createFuncs eenv ng tenv' M.empty (createDeepSeqName . fst) createDeepSeqStore (createDeepSeqExpr tenv)

createDeepSeqName ::  Name -> Name
createDeepSeqName n = Name ("walk" `T.append` nameOcc n) Nothing 0 (loc n)

createDeepSeqStore :: (Name, AlgDataTy) -> Name -> Walkers -> Walkers
createDeepSeqStore (n, adt) n' w =
    let
        bn = bound_names adt
        bnt = map (TyVar . flip Id TYPE) bn
        bnf = map (\b -> TyFun b b) bnt

        base = TyFun (TyConApp n []) (TyConApp n [])

        t = foldr TyFun base (bnt ++ bnf)
        i = Id n' t
    in
    M.insert n i w

createDeepSeqExpr :: TypeEnv -> Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
createDeepSeqExpr tenv w (n, adt) ng =
    let
        bn = bound_names adt

        -- Generates fresh names for TYPE variables, and walker function variables
        (bn', ng') = freshNames (length bn) ng
        (wbn, ng'') = freshNames (length bn) ng'

        bni = map (flip Id TYPE) bn'
        wbni = map (\(b, f) -> Id f (TyFun (TyVar (Id b TYPE)) (TyVar (Id b TYPE)))) $ zip bn' wbn

        bfuncs = zip bn' wbni

        adt' = renames (HM.fromList (zip bn bn')) adt

        (e, ng''') = createDeepSeqCase1 tenv w bfuncs n bn' adt' ng''
    in
    (foldr Lam e (bni ++ wbni), ng''')

createDeepSeqCase1 :: TypeEnv -> Walkers -> [(Name, Id)] -> Name -> [BoundName] -> AlgDataTy -> NameGen -> (Expr, NameGen)
createDeepSeqCase1 tenv w ti n bn (DataTyCon {data_cons = dc}) ng =
    let
        (i, ng') = freshId (TyConApp n $ map (TyVar . flip Id TYPE) bn) ng
        (caseB, ng'') = freshId (TyConApp n $ map (TyVar . flip Id TYPE) bn) ng'

        (alts, ng''') = createDeepSeqDataConCase1Alts tenv w ti n caseB bn ng'' dc

        c = Case (Var i) caseB alts
    in
    (Lam i c, ng''')
createDeepSeqCase1 _ w ti n bn (NewTyCon {rep_type = t}) ng =
    let
        t' = TyConApp n $ map (TyVar . flip Id TYPE) bn

        (i, ng') = freshId t' ng
        (caseB, ng'') = freshId t ng'

        cast = Cast (Var i) (t' :~ t)

        e = deepSeqFuncCall w ti (Var caseB)
        e' = Cast e (t :~ t')

        alt = Alt Default e'

        c = Case cast caseB [alt]
    in
    (Lam i c, ng'')
createDeepSeqCase1 _ _ _ _ _ _ _ = error "createDeepSeqCase1: bad argument passed"

createDeepSeqDataConCase1Alts :: TypeEnv -> Walkers -> [(Name, Id)] -> Name -> Id -> [BoundName] -> NameGen -> [DataCon] -> ([Alt], NameGen)
createDeepSeqDataConCase1Alts _ _ _ _ _ _ ng [] = ([], ng)
createDeepSeqDataConCase1Alts tenv w ti n i bn ng (dc@(DataCon _ _ ts):xs) =
    let
        (binds, ng') = freshIds ts ng

        dct = bindTypes (Data dc)

        (e, ng'') = createDeepSeqDataConCase2 tenv w ti binds ng' dct
        alt = Alt (DataAlt dc binds) e

        (alts, ng''') = createDeepSeqDataConCase1Alts tenv w ti n i bn ng'' xs
    in
    (alt:alts, ng''')

bindTypes :: Expr -> Expr
bindTypes e =
    let
        t = tyForAllIds $ typeOf e
        tb = map (Type . TyVar) t
    in
    foldl' App e tb

tyForAllIds :: Type -> [Id]
tyForAllIds (TyForAll (NamedTyBndr i) t) = i:tyForAllIds t
tyForAllIds _ = []

createDeepSeqDataConCase2 :: TypeEnv -> Walkers -> [(Name, Id)] -> [Id] -> NameGen -> Expr -> (Expr, NameGen)
createDeepSeqDataConCase2 _ _ _ [] ng e = (e, ng)
createDeepSeqDataConCase2 tenv w ti (i:is) ng e
    | t@(TyConApp n _) <- typeOf i 
    , Just (NewTyCon {rep_type = rt}) <- M.lookup n tenv =
    let
        (i', ng') = freshId rt ng

        b = deepSeqFuncCall w ti (Var i)
        bCast = Cast b (t :~ rt)

        vi = Var i'
        viCast = Cast vi (rt :~ t)

        (ae, ng'') = createDeepSeqDataConCase2 tenv w ti is ng' (App e viCast)
    in
    (Case bCast i' [Alt Default ae], ng'')
    | otherwise =
        let
            (i', ng') = freshId (typeOf i) ng

            b = deepSeqFuncCall w ti (Var i)

            (ae, ng'') = createDeepSeqDataConCase2 tenv w ti is ng' (App e (Var i'))
        in
        (Case b i' [Alt Default ae], ng'')

-- Calling a higher order function
deepSeqFuncCall :: Walkers -> [(Name, Id)] -> Expr -> Expr
deepSeqFuncCall w ti e =
    case deepSeqFunc w ti e of
        Just e' -> App e' e
        Nothing -> e

deepSeqFunc :: Typed t => Walkers -> [(Name, Id)] -> t -> Maybe Expr
deepSeqFunc w ti e
    | (TyConApp n ts) <- typeOf e
    , Just f <- M.lookup n w =
        let
            as = map Type ts
            as' = map (walkerFunc w ti) ts
        in
        Just $ foldl' App (Var f) (as ++ as')
    | (TyVar (Id n _)) <- typeOf e
    , Just f <- lookup n ti =
       Just $  Var f
    | otherwise = Nothing

walkerFunc :: Walkers -> [(Name, Id)] -> Type -> Expr
walkerFunc _ ti (TyVar (Id n _)) 
    | Just tyF <- lookup n ti = 
        Var tyF
walkerFunc w ti (TyConApp n ts)
    | Just f <- M.lookup n w =
        let
            as = map Type ts
            ft = mapMaybe (deepSeqFunc w ti . PresType) ts
        in
        foldl' App (Var f) (as ++ ft)
walkerFunc _ _ _ = error "walkerFunc: bad argument passed"