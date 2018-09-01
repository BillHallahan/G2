{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
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
createDeepSeqName n = Name ("walk" `T.append` nameOcc n) Nothing 0 (spanning n)

createDeepSeqStore :: (Name, AlgDataTy) -> Name -> Walkers -> Walkers
createDeepSeqStore (n, adt) n' w =
    let
        bn = map TyVar $ bound_ids adt
        bnf = map (\b -> TyFun b b) bn

        base = TyFun (TyConApp n TYPE) (TyConApp n TYPE)

        t = foldr TyFun base (bn ++ bnf)
        i = Id n' t
    in
    M.insert n i w

type RenameMap = HM.HashMap Name Name

createDeepSeqExpr :: TypeEnv -> Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
createDeepSeqExpr tenv w (n, adt) ng =
    let
        bn = bound_ids adt

        -- Generates fresh names for TYPE variables, and walker function variables
        (bn', ng') = freshNames (length bn) ng
        (wbn, ng'') = freshNames (length bn) ng'

        bni = map (flip Id TYPE) bn'
        wbni = map (\(b, f) -> Id f (TyFun (TyVar (Id b TYPE)) (TyVar (Id b TYPE)))) $ zip bn' wbn

        bfuncs = zip bn' wbni -- SUSPECT? bn' should be something else?
        rm = HM.fromList $ zip (map idName bn) bn'

        adt' = adt --renames (HM.fromList (zip (map idName bn) bn')) adt

        (e, ng''') = createDeepSeqCase1 tenv w bfuncs n rm bn' adt' ng''
    in
    (mkLams (map (TypeL,) bni ++ map (TermL,) wbni) e, ng''')

createDeepSeqCase1 :: TypeEnv -> Walkers -> [(Name, Id)] -> Name -> RenameMap-> [BoundName] -> AlgDataTy -> NameGen -> (Expr, NameGen)
createDeepSeqCase1 tenv w ti n rm bn (DataTyCon {data_cons = dc}) ng =
    let
        (i, ng') = freshId (mkTyConApp n (map (TyVar . flip Id TYPE) bn) TYPE) ng
        (caseB, ng'') = freshId (mkTyConApp n (map (TyVar . flip Id TYPE) bn) TYPE) ng'

        (alts, ng''') = createDeepSeqDataConCase1Alts tenv w ti n caseB rm bn ng'' dc

        c = Case (Var i) caseB alts
    in
    (Lam TermL i c, ng''')
createDeepSeqCase1 _ w ti n rm bn (NewTyCon {rep_type = t}) ng =
    let
        t' = mkTyConApp n (map (TyVar . flip Id TYPE) bn) TYPE

        (i, ng') = freshId t' ng
        (caseB, ng'') = freshId t ng'

        cast = Cast (Var i) (t' :~ t)

        e = deepSeqFuncCall w ti rm (Var caseB)
        e' = Cast e (t :~ t')

        alt = Alt Default e'

        c = Case cast caseB [alt]
    in
    (Lam TermL i c, ng'')
createDeepSeqCase1 _ _ _ _ _ _ _ _ = error "createDeepSeqCase1: bad argument passed"

createDeepSeqDataConCase1Alts :: TypeEnv -> Walkers -> [(Name, Id)] -> Name -> Id -> RenameMap -> [BoundName] -> NameGen -> [DataCon] -> ([Alt], NameGen)
createDeepSeqDataConCase1Alts _ _ _ _ _ _ _ ng [] = ([], ng)
createDeepSeqDataConCase1Alts tenv w ti n i rm bn ng (dc@(DataCon _ t):xs) =
    let
        ts = renames rm $ anonArgumentTypes dc

        (binds, ng') = freshIds ts ng

        dct = bindTypes rm (Data dc)

        (e, ng'') = createDeepSeqDataConCase2 tenv w ti rm binds ng' dct
        alt = Alt (DataAlt dc binds) e

        (alts, ng''') = createDeepSeqDataConCase1Alts tenv w ti n i rm bn ng'' xs
    in
    (alt:alts, ng''')

bindTypes :: RenameMap -> Expr -> Expr
bindTypes rm e =
    let
        t = tyForAllIds $ typeOf e
        tb = map (Type . TyVar . renames rm) t
    in
    foldl' App e tb

tyForAllIds :: Type -> [Id]
tyForAllIds (TyForAll (NamedTyBndr i) t) = i:tyForAllIds t
tyForAllIds _ = []

createDeepSeqDataConCase2 :: TypeEnv -> Walkers -> [(Name, Id)] -> RenameMap -> [Id] -> NameGen -> Expr -> (Expr, NameGen)
createDeepSeqDataConCase2 _ _ _ _ [] ng e = (e, ng)
createDeepSeqDataConCase2 tenv w ti rm (i:is) ng e
    | t@(TyConApp n _) <- typeOf i 
    , Just (NewTyCon {rep_type = rt}) <- M.lookup n tenv =
    let
        (i', ng') = freshId rt ng

        b = deepSeqFuncCall w ti rm (Var i)
        bCast = Cast b (t :~ rt)

        vi = Var i'
        viCast = Cast vi (rt :~ t)

        (ae, ng'') = createDeepSeqDataConCase2 tenv w ti rm is ng' (App e viCast)
    in
    (Case bCast i' [Alt Default ae], ng'')
    | otherwise =
        let
            (i', ng') = freshId (typeOf i) ng

            b = deepSeqFuncCall w ti rm (Var i)

            (ae, ng'') = createDeepSeqDataConCase2 tenv w ti rm is ng' (App e (Var i'))
        in
        (Case b i' [Alt Default ae], ng'')

-- Calling a higher order function
deepSeqFuncCall :: Walkers -> [(Name, Id)] -> RenameMap -> Expr -> Expr
deepSeqFuncCall w ti rm e =
    case deepSeqFunc w ti rm e of
        Just e' -> App e' e
        Nothing -> e

deepSeqFunc :: Typed t => Walkers -> [(Name, Id)] -> RenameMap -> t -> Maybe Expr
deepSeqFunc w ti rm e
    | t <- typeOf e
    , TyConApp n _ <- tyAppCenter t
    , ts <- tyAppArgs t
    , Just f <- M.lookup n w =
        let
            as = map Type $ renames rm ts
            as' = map (walkerFunc w ti rm) ts
        in
        Just $ foldl' App (Var f) (as ++ as')
    | (TyVar (Id n _)) <- typeOf e
    , Just f <- lookup n ti =
       Just $  Var f
    | otherwise = Nothing

walkerFunc :: Walkers -> [(Name, Id)] -> RenameMap -> Type -> Expr
walkerFunc _ ti rm (TyVar (Id n _))
    | Just tyF <- lookup n ti = 
        Var tyF
walkerFunc w ti rm t
    | TyConApp n _ <- tyAppCenter t
    , ts <- tyAppArgs t
    , Just f <- M.lookup n w =
        let
            as = renames rm $ map Type ts
            ft = renames rm $ mapMaybe (deepSeqFunc w ti rm . PresType) ts
        in
        foldl' App (Var f) (as ++ ft)
walkerFunc _ ni _ t = error $ "walkerFunc: bad argument passed" ++ "\n" ++ show ni ++ "\n" ++ show t