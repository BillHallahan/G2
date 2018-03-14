{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.TCGen (createLHTC, genTC) where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Liquid.TCValues

import Data.Coerce
import Data.Foldable
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import Debug.Trace

---------------------------------------
-- LH TypeClass Gen
---------------------------------------

-- genTC
-- The [(Name, Type, Walkers)] is
--  1) The name of a TC function
--  2) The type of the function
--  3) The instance of that function for all Types
-- We first generate a new dictionary type Dict for the TC.  Then we generate new functions
-- to get that Dict for each type.
genTC :: ExprEnv -> TypeEnv -> TypeClasses -> Name -> [(Name, Type, Walkers)] -> NameGen -> (ExprEnv, TypeEnv, TypeClasses, NameGen)
genTC eenv tenv tc tcn ntws ng =
    let
        (tcn', ng2) = (tcn, ng) --freshSeededName tcn ng

        (fn, ts, ws) = unzip3 ntws

        (dcN, ng3) = freshSeededName tcn ng2

        dc = DataCon dcN (mkTyFun (ts ++ [TyConApp dcN []])) ts

        adt = DataTyCon { bound_names = []
                        , data_cons = [dc] }

        tenv' = M.insert tcn' adt tenv

        -- Get type names
        ns = M.keys tenv'

        (eenv', ti, ng4) = genTCFuncs tcn' eenv tenv' [] ng3 dc ns ws

        (tci, ng5) = freshId TYPE ng4

        tc' = coerce . M.insert tcn' (Class { insts = ti, typ_ids = [tci] }) $ coerce tc

        --Create functions to access the TC functions
        (access, ng6) = mapNG (accessFunction tcn' dc) [0..length fn] ng5

        eenv'' = E.insertExprs (zip fn access) eenv'
    in
    (eenv'', tenv', tc', ng6)

genTCFuncs :: Name ->  ExprEnv -> TypeEnv -> [(Type, Id)] -> NameGen -> DataCon -> [Name] -> [Walkers] -> (ExprEnv, [(Type, Id)], NameGen)
genTCFuncs _ eenv _ ti ng _ [] _ = (eenv, ti, ng)
genTCFuncs lh eenv tenv ti ng dc (n:ns) ws =
    let
        (fn, ng') = lhFuncName n ng

        t = M.lookup n tenv

        bn = case fmap bound_names t of
            Just bn' -> bn'
            Nothing -> error "Bound names not found in genTCFuncs"

        bni = map (flip Id TYPE) bn

        bnv = map TyVar bni
        tbnv = map Type bnv
        -- lhbnv = map (\bt -> Var $ Id (Name "DICT" Nothing 0) (TyConApp lh [bt])) bnv

        fs = mapMaybe (M.lookup n) ws
        vs = map Var fs
        vs' = map (\v -> mkApp $ v:tbnv) vs

        e = mkLams bni $ mkApp $ Data dc:vs'

        eenv' = E.insert fn e eenv

        t' = TyConApp lh [TyConApp n bnv]

        ti' = (TyConApp n bnv, Id fn t'):ti
    in
    genTCFuncs lh eenv' tenv ti' ng' dc ns ws

lhFuncName :: Name -> NameGen -> (Name, NameGen)
lhFuncName (Name n _ _) ng = freshSeededString ("lh" `T.append` n `T.append` "Func") ng

-- | accessFunction
--Create a function to access a TC function from the ADT
accessFunction :: Name -> DataCon -> Int -> NameGen -> (Expr, NameGen)
accessFunction tcn dc@(DataCon _ _ ts) i ng =
    let
        t = TyConApp tcn []

        -- This gets bound to the Type (Expr constructor) argument
        (tb, ng2) = freshId TYPE ng

        (lb, ng3) = freshId t ng2
        (cb, ng4) = freshId t ng3

        (is, ng5) = freshIds ts ng4

        a = Alt (DataAlt dc is) $ Var (is !! i)

        c = Case (Var lb) cb [a]
    in
    (Lam lb (Lam tb c), ng5)

createLHTC :: State h t -> ExprEnv -> (State h t, ExprEnv, TCValues)
createLHTC s@(State { expr_env = eenv
                    , type_env = tenv
                    , name_gen = ng
                    , known_values = kv
                    , type_classes = tc }) meenv =
    let
        tenv' = M.toList tenv

        ([lhTCN, lhEqN, lhNeN, lhLtN, lhLeN, lhGtN, lhGeN, lhPPN], ng2) = 
            freshSeededStrings ["LH", "LHEq", "LHNe", "LHlt", "LHle", "LHgt", "LHge", "LHpp"] ng

        (meenv2, ng3, eq_w) = createFuncs meenv ng2 tenv' M.empty (lhEqName . fst) lhStore (lhTEnvExpr lhTCN (lhEqCase2Alts lhEqN) (eqLHFuncCall lhEqN) meenv tenv kv)
        (meenv3, ng4, neq_w) = createFuncs meenv2 ng3 tenv' M.empty (lhNeqName . fst) lhStore (lhNeqExpr lhTCN eq_w meenv2)
        (meenv4, ng5, lt_w) = createFuncs meenv3 ng4 tenv' M.empty (lhLtName . fst) lhStore (lhTEnvExpr lhTCN (lhLtCase2Alts lhLtN) (ltLHFuncCall lhLtN) meenv3 tenv kv)
        (meenv5, ng6, le_w) = createFuncs meenv4 ng5 tenv' M.empty (lhLeName . fst) lhStore (lhLeExpr lt_w eq_w meenv4)
        (meenv6, ng7, gt_w) = createFuncs meenv5 ng6 tenv' M.empty (lhGtName . fst) lhStore (lhGtExpr lt_w meenv5)
        (meenv7, ng8, ge_w) = createFuncs meenv6 ng7 tenv' M.empty (lhGeName . fst) lhStore (lhGeExpr le_w meenv6)

        (meenv8, ng9, pp_w) = createFuncs meenv7 ng8 tenv' M.empty (lhPolyPredName . fst) lhStore (lhPolyPred meenv7 tenv lhTCN kv)

        tb = tyBool kv

        (tvAN, ng10) = freshSeededString "a" ng9
        tvA = TyVar $ Id tvAN TYPE

        (meenv9, tenv'', tc', ng11) = genTC meenv8 tenv tc lhTCN
                        [ (lhEqN, TyFun tvA (TyFun tvA tb), eq_w) 
                        , (lhNeN, TyFun tvA (TyFun tvA tb), neq_w)
                        , (lhLtN, TyFun tvA (TyFun tvA tb), lt_w)
                        , (lhLeN, TyFun tvA (TyFun tvA tb), le_w)
                        , (lhGtN, TyFun tvA (TyFun tvA tb), gt_w)
                        , (lhGeN, TyFun tvA (TyFun tvA tb), ge_w)
                        , (lhPPN, TyFun (TyFun tvA tb) tb, pp_w) ] ng10

        tcv = TCValues {lhTC = lhTCN, lhEq = lhEqN, lhNe = lhNeN, lhLt = lhLtN, lhLe = lhLeN, lhGt = lhGtN, lhGe = lhGeN, lhPP = lhPPN}
    in
    (s { name_gen = ng11, type_env = tenv'', type_classes = tc' }, meenv9, tcv)

---------------------------------------
-- Gen Helper
---------------------------------------

lhStore :: (Name, AlgDataTy) -> Name -> Walkers -> Walkers
lhStore (n, adt) n' w =
    let
        bn = bound_names adt
        bnt = map (TyVar . flip Id TYPE) bn
        bnf = map (\b -> TyFun b b) bnt

        base = TyFun (TyConApp n []) (TyConApp n [])

        t = foldr TyFun base (bnt ++ bnf)
        i = Id n' t
    in
    M.insert n i w

-- Returns bindings for TYPE parameters and cooresponding LH typeclasses
boundNameBindings :: Name -> AlgDataTy -> NameGen -> (AlgDataTy, [Id], [Id], NameGen)
boundNameBindings lh adt ng =
    let
        bn = bound_names adt

        -- Generates fresh names for TYPE variables, and eq function variables
        (bn', ng') = freshNames (length bn) ng
        (wbn, ng'') = freshNames (length bn) ng'

        bni = map (flip Id TYPE) bn'
        wbni = map (\(b, f) -> Id f (TyConApp lh [TyVar (Id b TYPE)])) $ zip bn' wbn

        adt' = foldr (uncurry rename) adt (zip bn bn')
    in
    (adt', bni, wbni, ng'')

---------------------------------------
-- Eq/Ne/Ord Function Gen
---------------------------------------


lhEqName :: Name -> Name
lhEqName (Name n _ _) = Name ("lhEqName" `T.append` n) Nothing 0

lhTEnvExpr :: Name -> Case2Alts -> LHFuncCall -> ExprEnv -> TypeEnv -> KnownValues -> Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
lhTEnvExpr lh ca fc eenv tenv kv w (n, adt) ng =
    let
        (adt', bni, wbni, ng'') = boundNameBindings lh adt ng

        bn' = (map idName bni)

        bfuncs = zip bn' wbni

        (e, ng''') = lhTEnvCase ca fc eenv tenv kv w bfuncs n bn' adt' ng''
    in
    (foldr Lam e (wbni ++ bni), ng''')

lhTEnvCase :: Case2Alts -> LHFuncCall -> ExprEnv -> TypeEnv -> KnownValues -> Walkers -> [(Name, Id)] -> Name -> [Name] -> AlgDataTy -> NameGen -> (Expr, NameGen)
lhTEnvCase ca _ eenv tenv kv w ti n bn (DataTyCon {data_cons = dc}) ng =
    let
        t = TyConApp n $ map (TyVar . flip Id TYPE) bn

        (i1, ng2) = freshId t ng
        (caseB, ng3) = freshId t ng2

        (i2, ng4) = freshId t ng3

        (alts, ng5) = lhTEnvDataConAlts ca eenv tenv kv w ti n caseB i2 bn  ng4 dc

        c = Case (Var i1) caseB alts
    in
    (Lam i1 (Lam i2 c), ng5)
lhTEnvCase _ fc eenv tenv kv w ti _ bn (NewTyCon { rep_type = t@(TyConApp n _) }) ng =
    let
        t' = TyConApp n $ map (TyVar . flip Id TYPE) bn

        (i1, ng2) = freshId t ng
        (i2, ng3) = freshId t ng2

        v1 = Cast (Var i1) (t' :~ t)
        v2 = Cast (Var i2) (t' :~ t)

        e = fc eenv tenv kv w ti v1 v2
    in
    (Lam i1 (Lam i2 e), ng3)
lhTEnvCase _ _ _ _ _ _ _ _ _ _ ng = (Var (Id (Name "BADlhTEnvCase" Nothing 0) TyUnknown), ng)

lhTEnvDataConAlts :: Case2Alts -> ExprEnv -> TypeEnv -> KnownValues -> Walkers -> [(Name, Id)] -> Name -> Id -> Id -> [Name] -> NameGen -> [DataCon] -> ([Alt], NameGen)
lhTEnvDataConAlts _ _ _ _ _ _ _ _ _ _ ng [] = ([], ng)
lhTEnvDataConAlts ca eenv tenv kv w ti n caseB1 i2 bn ng (dc@(DataCon _ t ts):xs) =
    let
        (binds1, ng2) = freshIds ts ng

        (caseB2, ng3) = freshId t ng2

        (cAlts, ng4) = ca eenv tenv kv w ti caseB1 caseB2 binds1 dc ng3

        c = Case (Var i2) caseB2 cAlts
            
        alt = Alt (DataAlt dc binds1) c

        (alts, ng5) = lhTEnvDataConAlts ca eenv tenv kv w ti n caseB1 i2 bn ng4 xs
    in
    (alt:alts, ng5)

type Case2Alts = ExprEnv -> TypeEnv -> KnownValues -> Walkers -> [(Name, Id)] -> Id -> Id -> [Id] -> DataCon -> NameGen -> ([Alt], NameGen)

lhEqCase2Alts :: Name -> Case2Alts
lhEqCase2Alts lhExN eenv tenv kv w ti _ _ binds1 dc@(DataCon _ _ ts) ng =
    let
        (binds2, ng2) = freshIds ts ng

        true = mkTrue kv tenv
        false = mkFalse kv tenv

        -- Check that the two DataCons args are equal
        zbinds = zip (map Var binds1) (map Var binds2)

        b = tyBool kv
        pt = TyFun b (TyFun b b)

        e = foldr (\e' -> App (App (mkAnd eenv) e')) true
          $ map (uncurry (eqLHFuncCall lhExN eenv tenv kv w ti)) zbinds
    in
     ([ Alt (DataAlt dc binds2) e
      , Alt Default false ]
     , ng2)

type LHFuncCall = ExprEnv -> TypeEnv -> KnownValues ->  Walkers -> [(Name, Id)] -> Expr -> Expr -> Expr

eqLHFuncCall :: Name -> LHFuncCall
eqLHFuncCall lhExN _ tenv kv w ti e e'
    | (TyConApp n ts) <- typeOf e
    , Just f <- M.lookup n w =
        let
            as = map Type ts
        in
        foldl' App (Var f) (as ++ [e, e'])
    | t@(TyVar (Id n _)) <- typeOf e
    , Just f <- lookup n ti =
        let
            c = App (Var (Id lhExN TyUnknown)) (Type t)
        in
        App (App c e) e'
    | TyFun _ _ <- typeOf e =
        mkTrue kv tenv
    | t <- typeOf e
    ,  t == TyLitInt
    || t == TyLitDouble
    || t == TyLitFloat
    || t == TyLitChar =
        let
            b = tyBool kv
            pt = TyFun t (TyFun t b)
        in
        App (App (Prim Eq pt) e) e'
    | otherwise = error $ "\nError in eqLHFuncCall" ++ show (typeOf e)

eqFunc :: Walkers -> [(Name, Id)] -> Type -> Expr
eqFunc _ ti (TyVar (Id n _)) 
    | Just tyF <- lookup n ti = 
        Var tyF
eqFunc w _ (TyConApp n _)
    | Just f <- M.lookup n w =
       Var f

lhNeqName :: Name -> Name
lhNeqName (Name n _ _) = Name ("lhNeName" `T.append` n) Nothing 0

lhNeqExpr :: Name -> Walkers -> ExprEnv -> Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
lhNeqExpr lh eqW eenv _ (n, _) ng = 
    let
        f = case M.lookup n eqW of
            Just f' -> f'
            Nothing -> error "Unknown function in lhNeqExpr"
        fe = case E.lookup (idName f) eenv of
            Just fe' -> fe'
            Nothing -> error "Unknown function def in lhNeqExpr"
        li = leadingLamIds fe

        no = mkNot eenv

        nli = map idName li
        (li', ng') = doRenames nli ng li

        fApp = foldl' App (Var f) $ map Var $ filter (not . isTC lh) li'

        e = foldr Lam (App no fApp) li'
    in
    (e, ng')

isTC :: Name -> Id -> Bool
isTC n (Id _ (TyConApp n' _)) = n == n'
isTC _ _ = False

lhLtName :: Name -> Name
lhLtName (Name n _ _) = Name ("lhLtName" `T.append` n) Nothing 0

-- Once we have the first datacon (dc1) selected, we have to branch on all datacons less than dc1
lhLtCase2Alts :: Name -> ExprEnv -> TypeEnv -> KnownValues -> Walkers -> [(Name, Id)] -> Id -> Id -> [Id] -> DataCon -> NameGen -> ([Alt], NameGen)
lhLtCase2Alts lhExN eenv tenv kv w ti caseB1 _ binds1 dc@(DataCon dcn _ _) ng =
    let
        true = mkTrue kv tenv
        false = mkFalse kv tenv

        t = typeOf caseB1

        adt = case t of
                (TyConApp n' _) -> M.lookup n' tenv
                _ -> error "Bad type in lhLtCase2Alts"

        dcs = fmap (takeWhile ((/=) dcn . dataConName) . dataCon) adt
        (la, ng2) = maybe ([], ng) (lhLtDCAlts true ng) dcs

        (asame, ng3) = lhLtSameAlt lhExN eenv tenv kv w ti binds1 ng2 dc
    in
    (Alt Default false:asame:la
    , ng3)

lhLtDCAlts :: Expr -> NameGen -> [DataCon] -> ([Alt], NameGen)
lhLtDCAlts _ ng [] = ([], ng)
lhLtDCAlts true ng (dc@(DataCon _ _ ts):dcs) = 
    let
        (binds2, ng2) = freshIds ts ng

        alt = Alt (DataAlt dc binds2) true

        (alts, ng3) = lhLtDCAlts true ng2 dcs
    in
    (alt:alts, ng3)

lhLtSameAlt :: Name -> ExprEnv -> TypeEnv -> KnownValues -> Walkers -> [(Name, Id)] -> [Id] -> NameGen -> DataCon -> (Alt, NameGen)
lhLtSameAlt lhExN eenv tenv kv w ti binds1 ng dc@(DataCon _ _ ts) =
    let
        (binds2, ng2) = freshIds ts ng

        zbinds = zip (map Var binds1) (map Var binds2)

        ltB = map (uncurry (ltLHFuncCall lhExN eenv tenv kv w ti)) zbinds
        eqB = map (uncurry (eqLHFuncCall lhExN eenv tenv kv w ti)) zbinds

        zipB = zip ltB eqB

        (e, ng3) = lhLtSameAltCases tenv kv ng2 zipB
    in
    (Alt (DataAlt dc binds2) e, ng3)

lhLtSameAltCases :: TypeEnv -> KnownValues -> NameGen -> [(Expr, Expr)] -> (Expr, NameGen)
lhLtSameAltCases tenv kv ng [] = (mkFalse kv tenv, ng)
lhLtSameAltCases tenv kv ng ((lt, eq):xs) =
    let
        (Data true) = mkTrue kv tenv
        (Data false) = mkFalse kv tenv

        (e, ng2) = lhLtSameAltCases tenv kv ng xs

        b = tyBool kv
    
        ([b1, b2], ng3) = freshIds [b, b] ng2

        c = Case lt b1 
            [ Alt (DataAlt true []) (Data true)
            , Alt Default 
                (Case eq b2 
                    [ Alt (DataAlt true []) e
                    , Alt Default (Data false)]
                )
            ]
    in
    (c, ng3)

ltLHFuncCall :: Name -> LHFuncCall
ltLHFuncCall lhExN _ tenv kv w ti e e'
    | (TyConApp n ts) <- typeOf e
    , Just f <- M.lookup n w =
        let
            as = map Type ts
        in
        foldl' App (Var f) (as ++ [e, e'])
    | t@(TyVar (Id n _)) <- typeOf e
    , Just f <- lookup n ti =
        let
            c = App (Var (Id lhExN TyUnknown)) (Type t)
        in
        App (App c e) e'
    | TyFun _ _ <- typeOf e =
        mkTrue kv tenv
    | t <- typeOf e
    ,  t == TyLitInt
    || t == TyLitDouble
    || t == TyLitFloat
    || t == TyLitChar =
        let
            b = tyBool kv
            pt = TyFun t (TyFun t b)
        in
        App (App (Prim Lt pt) e) e'
    | otherwise = error $ "\nError in ltLHFuncCall" ++ show (typeOf e)

ltFunc :: Walkers -> [(Name, Id)] -> Type -> Expr
ltFunc _ ti (TyVar (Id n _)) 
    | Just tyF <- lookup n ti = 
        Var tyF
ltFunc w _ (TyConApp n _)
    | Just f <- M.lookup n w =
       Var f

dataConName :: DataCon -> Name
dataConName (DataCon n _ _) = n


lhLeName :: Name -> Name
lhLeName (Name n _ _) = Name ("lhLeName" `T.append` n) Nothing 0

lhLeExpr :: Walkers -> Walkers -> ExprEnv -> Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
lhLeExpr ltW eqW eenv _ (n, _) ng = 
    let
        lt = case M.lookup n ltW of
            Just f' -> f'
            Nothing -> error "Unknown function in lhLeExpr"
        eq = case M.lookup n eqW of
            Just f' -> f'
            Nothing -> error "Unknown function in lhLeExpr"
        fe = case E.lookup (idName eq) eenv of
            Just fe' -> fe'
            Nothing -> error "Unknown function def in lhLeExpr"
        li = leadingLamIds fe

        or_ex = mkOr eenv

        (li', ng') = freshIds (map typeOf li) ng

        ltApp = foldl' App (Var lt) $ map Var li'
        eqApp = foldl' App (Var eq) $ map Var li'

        orApp = App (App or_ex ltApp) eqApp

        e = foldr Lam orApp li'
    in
    (e, ng')

lhGtName :: Name -> Name
lhGtName (Name n _ _) = Name ("lhGtName" `T.append` n) Nothing 0

lhGtExpr :: Walkers -> ExprEnv -> Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
lhGtExpr ltW eenv _ (n, _) ng = 
    let
        f = case M.lookup n ltW of
            Just f' -> f'
            Nothing -> error "Unknown function in lhGtExpr"
        fe = case E.lookup (idName f) eenv of
            Just fe' -> fe'
            Nothing -> error "Unknown function def in lhGtExpr"
        li = leadingLamIds fe

        (li', ng') = freshIds (map typeOf li) ng

        fApp = foldl' App (Var f) $ map Var $ flipLastTwo li'

        e = foldr Lam fApp li'
    in
    (e, ng')

lhGeName :: Name -> Name
lhGeName (Name n _ _) = Name ("lhGeName" `T.append` n) Nothing 0

lhGeExpr :: Walkers -> ExprEnv -> Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
lhGeExpr leW eenv _ (n, _) ng = 
    let
        f = case M.lookup n leW of
            Just f' -> f'
            Nothing -> error "Unknown function in lhGeExpr"
        fe = case E.lookup (idName f) eenv of
            Just fe' -> fe'
            Nothing -> error "Unknown function def in lhGeExpr"
        li = leadingLamIds fe

        (li', ng') = freshIds (map typeOf li) ng

        fApp = foldl' App (Var f) $ map Var $ flipLastTwo li'

        e = foldr Lam fApp li'
    in
    (e, ng')

flipLastTwo :: [a] -> [a]
flipLastTwo (x:y:[]) = y:[x]
flipLastTwo (x:xs) = x:flipLastTwo xs
flipLastTwo xs = xs

---------------------------------------
-- DataType Ref Gen
---------------------------------------
lhPolyPredName :: Name -> Name
lhPolyPredName (Name n _ _) = Name ("lhPolyPred" `T.append` n) Nothing 0

lhPolyPred :: ExprEnv -> TypeEnv -> Name -> KnownValues -> Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
lhPolyPred eenv tenv lh kv w (n, adt) ng =
    let
        (adt', bni, _, ng2) = boundNameBindings lh adt ng
        bn = map idName bni

        tb = tyBool kv
        (fbi, ng3) = freshIds (map (\i -> TyFun (TyVar i) tb) bni) ng2

        bnf = zip bn fbi

        (e, ng4) = lhPolyPredCase eenv tenv kv w n adt' bn bnf ng3
    in
    (foldr Lam e (bni ++ fbi), ng4)

lhPolyPredCase :: ExprEnv -> TypeEnv -> KnownValues -> Walkers -> Name -> AlgDataTy -> [Name] -> [(Name, Id)] -> NameGen -> (Expr, NameGen)
lhPolyPredCase eenv tenv kv w n (DataTyCon { data_cons = dc }) bn bnf ng =
    let
        t = TyConApp n $ map (TyVar . flip Id TYPE) bn

        (i1, ng2) = freshId t ng
        (caseB, ng3) = freshId t ng2

        (alts, ng4) = lhPolyPredAlts eenv tenv kv w dc bnf ng3

        c = Case (Var i1) caseB alts
    in
    (Lam i1 c, ng4)
lhPolyPredCase _ tenv kv w n (NewTyCon { rep_type = t }) bn bnf ng =
    let
        t' = TyConApp n $ map (TyVar . flip Id TYPE) bn

        (i, ng2) = freshId t' ng
        (caseB, ng3) = freshId t ng2

        cast = Cast (Var i) (t' :~ t)

        e = polyPredLHFuncCall (mkTrue kv tenv) w bnf (Var caseB)

        alt = Alt Default e

        c = Case cast caseB [alt]
    in
    (Lam i c, ng3)


lhPolyPredAlts :: ExprEnv -> TypeEnv -> KnownValues -> Walkers -> [DataCon] -> [(Name, Id)] -> NameGen -> ([Alt], NameGen)
lhPolyPredAlts _ _ _ _ [] _ ng = ([], ng)
lhPolyPredAlts eenv tenv kv w (dc@(DataCon _ _ ts):dcs) bnf ng =
    let
        (binds, ng2) = freshIds ts ng
        
        e = lhPolyPredCaseExpr eenv tenv kv w binds bnf

        alt = Alt (DataAlt dc binds) e

        (alts, ng3) = lhPolyPredAlts eenv tenv kv w dcs bnf ng2
    in
    (alt:alts, ng3)

lhPolyPredCaseExpr :: ExprEnv -> TypeEnv -> KnownValues -> Walkers -> [Id] -> [(Name, Id)] -> Expr
lhPolyPredCaseExpr eenv tenv kv w bn bnf =
    let
        tyvs = filter (isTyVar . typeOf) bn
        ety = map (Type . typeOf) tyvs

        fns = [] -- map Var $ mapMaybe (flip lookup bnf) $ mapMaybe (tyVName . typeOf) tyvs

        pc = map (predCalls bnf) tyvs 
    
        an = mkAnd eenv
        true = mkTrue kv tenv

        fs = map (polyPredLHFuncCall true w bnf . Var) $ filter (not . isTyVar . typeOf) bn
    in
    foldr (\e -> App (App an e)) true $ pc ++ fns ++ fs

tyVName :: Type -> Maybe Name
tyVName (TyVar (Id n _)) = Just n
tyVName _ = Nothing

predCalls :: [(Name, Id)] -> Id -> Expr
predCalls bnf i@(Id _ (TyVar tvi)) =
    let
        fi = lookup (idName tvi) bnf
    in
    case fi of
        Just fi' -> App (Var fi') (Var i)
        Nothing -> error $ "No function found in predCalls " ++ show i ++ "\n" ++ show bnf

polyPredLHFuncCall :: Expr -> Walkers -> [(Name, Id)] -> Expr -> Expr
polyPredLHFuncCall true w bnf i = App (polyPredLHFunc' true w bnf i) i
    -- | TyConApp n ts <- typeOf i
    -- , Just f <- M.lookup n w =
    --     let
    --         as = map Type ts
    --         as' = map (polyPredFunc' w bnf) ts
    --     in
    --     foldl' App (Var f) (as ++ as' ++ [i])
    -- | TyFun _ _ <- typeOf i = true
    -- | t <- typeOf i
    -- ,  t == TyLitInt
    -- || t == TyLitDouble
    -- || t == TyLitFloat
    -- || t == TyLitChar = true
    -- | otherwise = error $ "Unhandled type " ++ show (typeOf i)

polyPredLHFunc' :: Typed t => Expr -> Walkers -> [(Name, Id)] -> t -> Expr
polyPredLHFunc' true w bnf i
    | TyConApp n ts <- typeOf i
    , Just f <- M.lookup n w =
        let
            as = map Type ts
            as' = map (polyPredFunc' true w bnf) ts
        in
        foldl' App (Var f) (as ++ as')
    | TyFun _ _ <- typeOf i = Lam (Id (Name "nonused_id" Nothing 0) (typeOf i)) true
    | t <- typeOf i
    ,  t == TyLitInt
    || t == TyLitDouble
    || t == TyLitFloat
    || t == TyLitChar = Lam (Id (Name "nonused_id" Nothing 0) (typeOf i)) true
    | TyVar _ <- typeOf i = polyPredFunc' true w bnf (typeOf i)
    | otherwise = error $ "Unhandled type " ++ show (typeOf i)

polyPredFunc' :: Expr ->  Walkers -> [(Name, Id)] -> Type -> Expr
polyPredFunc' _ _ bnf (TyVar (Id n _)) 
    | Just tyF <- lookup n bnf = 
        Var tyF
polyPredFunc' true w bnf (TyConApp n ts)
    | Just f <- M.lookup n w =
        let
            as = map Type ts
            ft = map (polyPredLHFunc' true w bnf . PresType) ts
        in
        foldl' App (Var f) (as ++ ft)
