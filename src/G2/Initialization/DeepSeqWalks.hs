{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
-- This module generates functions in the expr_env that walk over the whole structure of an ADT.
-- This forces evaluation of the ADT
module G2.Initialization.DeepSeqWalks (createDeepSeqWalks) where

import G2.Language

import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

type BoundName = Name

createDeepSeqWalks :: ExprEnv -> TypeEnv -> NameGen -> (ExprEnv, NameGen, Walkers)
createDeepSeqWalks eenv tenv ng =
    let
        tenv' = HM.toList tenv
    in
    createFuncs eenv ng tenv' M.empty (createDeepSeqName . fst) createDeepSeqStore (createDeepSeqExpr tenv)

createDeepSeqName ::  Name -> Name
createDeepSeqName n = Name ("walk" `T.append` nameOcc n) Nothing 0 (spanning n)

createDeepSeqStore :: (Name, AlgDataTy) -> Name -> Walkers -> Walkers
createDeepSeqStore (n, adt) n' w =
    let
        bi = bound_ids adt
        bn = map TyVar $ bound_ids adt
        bnf = map (\b -> TyFun b b) bn

        dc_t = foldr (const $ TyFun TYPE) TYPE [1..length bi]

        base = TyFun (TyCon n dc_t) (TyCon n dc_t)

        t = foldr TyFun base (bn ++ bnf)
        t' = foldr TyForAll t $ map NamedTyBndr bi
        i = Id n' t'
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
        (i, ng') = freshId (mkFullAppedTyCon n (map (TyVar . flip Id TYPE) bn) TYPE) ng
        (caseB, ng'') = freshId (mkFullAppedTyCon n (map (TyVar . flip Id TYPE) bn) TYPE) ng'

        (alts, ng''') = createDeepSeqDataConCase1Alts tenv w ti n caseB rm bn ng'' dc

        c = Case (Var i) caseB alts
    in
    (Lam TermL i c, ng''')
createDeepSeqCase1 _ w ti n rm bn (NewTyCon {rep_type = t}) ng =
    let
        t' = mkFullAppedTyCon n (map (TyVar . flip Id TYPE) bn) TYPE
        t'' = renames rm t

        (i, ng') = freshId t' ng
        (caseB, ng'') = freshId t'' ng'

        cast = Cast (Var i) (t' :~ t'')

        (e, ng''') = deepSeqFuncCall w ng'' ti rm (Var caseB)
        e' = Cast e (t'' :~ t')

        alt = Alt Default e'

        c = Case cast caseB [alt]
    in
    (Lam TermL i c, ng''')
createDeepSeqCase1 _ _ _ _ _ _ _ _ = error "createDeepSeqCase1: bad argument passed"

createDeepSeqDataConCase1Alts :: TypeEnv -> Walkers -> [(Name, Id)] -> Name -> Id -> RenameMap -> [BoundName] -> NameGen -> [DataCon] -> ([Alt], NameGen)
createDeepSeqDataConCase1Alts _ _ _ _ _ _ _ ng [] = ([], ng)
createDeepSeqDataConCase1Alts tenv w ti n i rm bn ng (dc@(DataCon _ _):xs) =
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
    | t@(TyCon n _) <- typeOf i 
    , Just (NewTyCon {rep_type = rt}) <- HM.lookup n tenv =
    let
        (i', ng') = freshId rt ng

        (b, ng'') = deepSeqFuncCall w ng' ti rm (Var i)
        bCast = Cast b (t :~ rt)

        vi = Var i'
        viCast = Cast vi (rt :~ t)

        (ae, ng''') = createDeepSeqDataConCase2 tenv w ti rm is ng'' (App e viCast)
    in
    (Case bCast i' [Alt Default ae], ng''')
    | otherwise =
        let
            (i', ng') = freshId (typeOf i) ng

            (b, ng'') = deepSeqFuncCall w ng' ti rm (Var i)

            (ae, ng''') = createDeepSeqDataConCase2 tenv w ti rm is ng'' (App e (Var i'))
        in
        (Case b i' [Alt Default ae], ng''')

-- Calling a higher order function
deepSeqFuncCall :: Walkers -> NameGen -> [(Name, Id)] -> RenameMap -> Expr -> (Expr, NameGen)
deepSeqFuncCall w ng ti rm e =
    case deepSeqFunc w ng ti rm e of
        Just (e', ng') -> (App e' e, ng')
        Nothing -> (e, ng)

deepSeqFunc :: Typed t => Walkers -> NameGen -> [(Name, Id)] -> RenameMap -> t -> Maybe (Expr, NameGen)
deepSeqFunc w ng ti rm e
    | t <- typeOf e
    , TyCon n _ <- tyAppCenter t
    , ts <- tyAppArgs t
    , Just f <- M.lookup n w =
        let
            as = map Type $ renames rm ts
            as' = map (walkerFunc w ti rm) ts
        in
        Just $ (foldl' App (Var f) (as ++ as'), ng)
    | t@(TyFun _ _) <- typeOf e =
        let
            (a_in, ng') = freshId t ng

            tys = anonArgumentTypes e
            (f_is, ng'') = freshIds tys ng' 
            
            cll = mkApp $ Var a_in:map Var f_is
            let_cll = Let (zip f_is $ map SymGen tys) cll

            (ds_cll, ng''') = deepSeqFuncCall w ng'' ti rm let_cll
            (bnd, ng'''') = freshId (typeOf ds_cll) ng'''

            (lam_ids, ng''''') = freshIds tys ng''''

            cse = Case ds_cll bnd [Alt Default $ mkLams (zip (repeat TermL) lam_ids) (Var bnd)]
        in
        Just (Lam TermL a_in cse, ng''''')
    | (TyVar (Id n _)) <- typeOf e
    , Just f <- lookup n ti =
       Just (Var f, ng)
    | otherwise = Nothing

walkerFunc :: Walkers -> [(Name, Id)] -> RenameMap -> Type -> Expr
walkerFunc _ ti _ (TyVar (Id n _))
    | Just tyF <- lookup n ti = 
        Var tyF
walkerFunc w ti rm t
    | TyCon n _ <- tyAppCenter t
    , ts <- tyAppArgs t
    , Just f <- M.lookup n w =
        let
            as = renames rm $ map Type ts
            ft = renames rm . map fst $ mapMaybe (deepSeqFunc w undefined ti rm . PresType) ts
        in
        foldl' App (Var f) (as ++ ft)
walkerFunc _ ni _ t = error $ "walkerFunc: bad argument passed" ++ "\n" ++ show ni ++ "\n" ++ show t
