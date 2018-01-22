module G2.Internals.Liquid.TCGen (createLHTC) where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Liquid.TCValues

import Data.Coerce
import Data.Foldable
import qualified Data.Map as M
import Data.Maybe

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
genTC eenv tenv tc tcn ntws@((_, _, w):_) ng =
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

        tc' = coerce . M.insert tcn' ti $ coerce tc

        --Create functions to access the TC functions
        (access, ng5) = mapNG (accessFunction tcn' dc) [0..length fn] ng4

        eenv'' = E.insertExprs (zip fn access) eenv'
    in
    (eenv'', tenv', tc', ng5)
genTC _ _ _ _ [] _ = error "No walkers given to genTC."

genTCFuncs :: Name ->  ExprEnv -> TypeEnv -> [(Type, Id)] -> NameGen -> DataCon -> [Name] -> [Walkers] -> (ExprEnv, [(Type, Id)], NameGen)
genTCFuncs _ eenv tenv ti ng _ [] _ = (eenv, ti, ng)
genTCFuncs lh eenv tenv ti ng dc (n:ns) ws =
    let
        (fn, ng') = lhFuncName n ng

        t = M.lookup n tenv

        bn = case fmap bound_names t of
            Just bn' -> bn'
            Nothing -> error "Bound names not found in genTCFuncs"

        bnv = map (TyVar . flip Id TYPE) bn

        fs = mapMaybe (M.lookup n) ws

        e = mkApp $ Data dc:map Var fs

        eenv' = E.insert fn e eenv

        t' = TyConApp lh [TyConApp n bnv]

        ti' = (TyConApp n bnv, Id fn t'):ti
    in
    genTCFuncs lh eenv' tenv ti' ng' dc ns ws

lhFuncName :: Name -> NameGen -> (Name, NameGen)
lhFuncName (Name n _ _) ng = freshSeededString ("lh" ++ n ++ "Func") ng

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

createLHTC :: State -> (State, Walkers, TCValues)
createLHTC s@(State { expr_env = eenv
                    , type_env = tenv
                    , name_gen = ng
                    , known_values = kv
                    , type_classes = tc }) =
    let
        tenv' = M.toList tenv

        ([lhTCN, lhEqN, lhNeN, lhLtN, lhLeN, lhGtN, lhGeN, lhPPN], ng2) = 
            freshSeededStrings ["LH", "LHEq", "LHNe", "LHlt", "LHle", "LHgt", "LHge", "LHpp"] ng

        lhEqE = Var (Id lhEqN $ TyFun tb (TyFun tb tb))
        lhLtE = Var (Id lhLtN $ TyFun tb (TyFun tb tb))

        (eenv2, ng3, eq_w) = createFuncs eenv ng2 tenv' M.empty (lhEqName . fst) lhStore (lhTEnvExpr lhTCN (lhEqCase2Alts) eqFuncCall eenv tenv kv)
        (eenv3, ng4, neq_w) = createFuncs eenv2 ng3 tenv' M.empty (lhNeqName . fst) lhStore (lhNeqExpr eq_w eenv2)
        (eenv4, ng5, lt_w) = createFuncs eenv3 ng4 tenv' M.empty (lhLtName . fst) lhStore (lhTEnvExpr lhTCN (lhLtCase2Alts lhEqE lhLtE) ltFuncCall eenv3 tenv kv)
        (eenv5, ng6, le_w) = createFuncs eenv4 ng5 tenv' M.empty (lhLeName . fst) lhStore (lhLeExpr lt_w eq_w eenv4)
        (eenv6, ng7, gt_w) = createFuncs eenv5 ng6 tenv' M.empty (lhGtName . fst) lhStore (lhGtExpr lt_w eenv5)
        (eenv7, ng8, ge_w) = createFuncs eenv6 ng7 tenv' M.empty (lhGeName . fst) lhStore (lhGeExpr le_w eenv6)

        (eenv8, ng9, pp_w) = createFuncs eenv7 ng8 tenv' M.empty (lhPolyPredName . fst) lhStore (lhPolyPred eenv7 tenv lhTCN kv)

        tb = tyBool kv

        (eenv9, tenv'', tc', ng10) = genTC eenv8 tenv tc lhTCN
                        [ (lhEqN, TyFun tb (TyFun tb tb), eq_w) 
                        , (lhNeN, TyFun tb (TyFun tb tb), neq_w)
                        , (lhLtN, TyFun tb (TyFun tb tb), lt_w)
                        , (lhLeN, TyFun tb (TyFun tb tb), le_w)
                        , (lhGtN, TyFun tb (TyFun tb tb), gt_w)
                        , (lhGeN, TyFun tb (TyFun tb tb), ge_w)
                        , (lhPPN, TyFun tb (TyFun tb tb), pp_w) ] ng9

        tcv = TCValues {lhTC = lhTCN, lhEq = lhEqN, lhNe = lhNeN, lhLt = lhLtN, lhLe = lhLeN, lhGt = lhGtN, lhGe = lhGeN, lhPP = lhPPN}
    in
    (s { expr_env = eenv9, name_gen = ng10, type_env = tenv'', type_classes = tc' }, eq_w, tcv)

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
boundNameBindings lhTC adt ng =
    let
        bn = bound_names adt

        -- Generates fresh names for TYPE variables, and eq function variables
        (bn', ng') = freshNames (length bn) ng
        (wbn, ng'') = freshNames (length bn) ng'

        bni = map (flip Id TYPE) bn'
        wbni = map (\(b, f) -> Id f (TyConApp lhTC [TyVar (Id b TYPE)])) $ zip bn' wbn

        adt' = foldr (uncurry rename) adt (zip bn bn')
    in
    (adt', bni, wbni, ng'')

---------------------------------------
-- Eq/Ne/Ord Function Gen
---------------------------------------


lhEqName :: Name -> Name
lhEqName (Name n _ _) = Name ("lhEqName" ++ n) Nothing 0

lhTEnvExpr :: Name -> Case2Alts -> FuncCall -> ExprEnv -> TypeEnv -> KnownValues -> Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
lhTEnvExpr lhTC ca fc eenv tenv kv w (n, adt) ng =
    let
        (adt', bni, wbni, ng'') = boundNameBindings lhTC adt ng

        bn' = (map idName bni)

        bfuncs = zip bn' wbni

        (e, ng''') = lhTEnvCase ca fc eenv tenv kv w bfuncs n bn' adt' ng''
    in
    (foldr Lam e (bni ++ wbni), ng''')

lhTEnvCase :: Case2Alts -> FuncCall -> ExprEnv -> TypeEnv -> KnownValues -> Walkers -> [(Name, Id)] -> Name -> [Name] -> AlgDataTy -> NameGen -> (Expr, NameGen)
lhTEnvCase ca _ eenv tenv kv w ti n bn adt@(DataTyCon {data_cons = dc}) ng =
    let
        t = TyConApp n $ map (TyVar . flip Id TYPE) bn

        (i1, ng2) = freshId t ng
        (caseB, ng3) = freshId t ng2

        (i2, ng4) = freshId t ng3

        (alts, ng5) = lhTEnvDataConAlts ca eenv tenv kv w ti n caseB i2 bn  ng4 dc

        c = Case (Var i1) caseB alts
    in
    (Lam i1 (Lam i2 c), ng5)
lhTEnvCase ca fc eenv tenv kv w ti _ bn (NewTyCon { rep_type = t@(TyConApp n _) }) ng =
    let
        t' = TyConApp n $ map (TyVar . flip Id TYPE) bn

        (i1, ng2) = freshId t ng
        (i2, ng3) = freshId t ng2

        v1 = Cast (Var i1) (t' :~ t)
        v2 = Cast (Var i2) (t' :~ t)

        e = fc eenv tenv kv w ti v1 v2
    in
    (Lam i1 (Lam i2 e), ng3)
lhTEnvCase _ _ _ _ _ _ _ _ _ _ ng = (Var (Id (Name "BADlhTEnvCase" Nothing 0) TyBottom), ng)

lhTEnvDataConAlts :: Case2Alts -> ExprEnv -> TypeEnv -> KnownValues -> Walkers -> [(Name, Id)] -> Name -> Id -> Id -> [Name] -> NameGen -> [DataCon] -> ([Alt], NameGen)
lhTEnvDataConAlts _ _ _ _ _ _ _ _ _ _ ng [] = ([], ng)
lhTEnvDataConAlts ca eenv tenv kv w ti n caseB1 i2 bn ng (dc@(DataCon dcn t ts):xs) =
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

lhEqCase2Alts :: Case2Alts
lhEqCase2Alts eenv tenv kv w ti caseB1 caseB2 binds1 dc@(DataCon dcn t ts) ng =
    let
        (binds2, ng2) = freshIds ts ng

        true = mkTrue kv tenv
        false = mkFalse kv tenv

        -- Check that the two DataCons args are equal
        zbinds = zip (map Var binds1) (map Var binds2)

        e = foldr (\e -> App (App (Prim And TyBottom) e)) true
          $ map (uncurry (eqFuncCall eenv tenv kv w ti)) zbinds
    in
     ([ Alt (DataAlt dc binds2) e
      , Alt Default false ]
     , ng2)

type FuncCall = ExprEnv -> TypeEnv -> KnownValues ->  Walkers -> [(Name, Id)] -> Expr -> Expr -> Expr

eqFuncCall :: FuncCall
eqFuncCall eenv tenv kv w ti e e'
    | (TyConApp n ts) <- typeOf e
    , Just f <- M.lookup n w =
        let
            as = map Type ts
            as' = map (eqFunc w ti) ts
        in
        foldl' App (Var f) (as ++ as' ++ [e, e'])
    | t@(TyVar (Id n _)) <- typeOf e
    , Just f <- lookup n ti =
        App (App (Var f) e) e'
    | TyFun _ _ <- typeOf e =
        mkTrue kv tenv
    | t <- typeOf e
    ,  t == TyLitInt
    || t == TyLitDouble
    || t == TyLitFloat
    || t == TyLitChar =
        let
            eq = mkEq eenv
        in
        App (App (Prim Eq TyBottom) e) e'
    | otherwise = error $ "\nError in eqFuncCall" ++ show (typeOf e)

eqFunc :: Walkers -> [(Name, Id)] -> Type -> Expr
eqFunc _ ti tyvar@(TyVar (Id n _)) 
    | Just tyF <- lookup n ti = 
        Var tyF
eqFunc w _ t@(TyConApp n _)
    | Just f <- M.lookup n w =
       Var f

lhNeqName :: Name -> Name
lhNeqName (Name n _ _) = Name ("lhNeName" ++ n) Nothing 0

lhNeqExpr :: Walkers -> ExprEnv -> Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
lhNeqExpr eqW eenv w (n, _) ng = 
    let
        f = case M.lookup n eqW of
            Just f' -> f'
            Nothing -> error "Unknown function in lhNeqExpr"
        fe = case E.lookup (idName f) eenv of
            Just fe' -> fe'
            Nothing -> error "Unknown function def in lhNeqExpr"
        li = leadingLamIds fe

        no = mkNot eenv

        (li', ng') = freshIds (map typeOf li) ng

        fApp = foldl' App (Var f) $ map Var li'

        e = foldr Lam (App no fApp) li'
    in
    (e, ng')

lhLtName :: Name -> Name
lhLtName (Name n _ _) = Name ("lhLtName" ++ n) Nothing 0

-- Once we have the first datacon (dc1) selected, we have to branch on all datacons less than dc1
lhLtCase2Alts :: Expr -> Expr -> Case2Alts
lhLtCase2Alts lhEq lhLt eenv tenv kv w ti caseB1 caseB2 binds1 dc@(DataCon dcn t ts) ng =
    let
        true = mkTrue kv tenv
        false = mkFalse kv tenv

        t = typeOf caseB1

        (n, adt) = case t of
                    (TyConApp n' _) -> (n', M.lookup n' tenv)
                    _ -> error "Bad type in lhLtCase2Alts"

        dcs = fmap (takeWhile ((/=) dcn . dataConName) . dataCon) adt
        (la, ng2) = maybe ([], ng) (lhLtDCAlts true ng) dcs

        (asame, ng3) = lhLtSameAlt lhEq lhLt eenv tenv kv w ti binds1 true false ng dc
    in
    (Alt Default false:asame:la
    , ng3)

lhLtDCAlts :: Expr -> NameGen -> [DataCon] -> ([Alt], NameGen)
lhLtDCAlts _ ng [] = ([], ng)
lhLtDCAlts true ng (dc@(DataCon dcn t ts):dcs) = 
    let
        (binds2, ng2) = freshIds ts ng

        alt = Alt (DataAlt dc binds2) true

        (alts, ng3) = lhLtDCAlts true ng2 dcs
    in
    (alt:alts, ng3)

lhLtSameAlt :: Expr -> Expr -> ExprEnv -> TypeEnv -> KnownValues -> Walkers -> [(Name, Id)] -> [Id] -> Expr -> Expr -> NameGen -> DataCon -> (Alt, NameGen)
lhLtSameAlt lhEq lhLt eenv tenv kv w ti binds1 true false ng dc@(DataCon _ _ ts) =
    let
        (binds2, ng2) = freshIds ts ng

        zbinds = zip (map Var binds1) (map Var binds2)

        ltB = map (uncurry (ltFuncCall eenv tenv kv w ti)) zbinds
        eqB = map (uncurry (eqFuncCall eenv tenv kv w ti)) zbinds

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
    
        ([b1, b2], ng3) = freshIds [TyBottom, TyBottom] ng2

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

ltFuncCall :: FuncCall
ltFuncCall eenv tenv kv w ti e e'
    | (TyConApp n ts) <- typeOf e
    , Just f <- M.lookup n w =
        let
            as = map Type ts
            as' = map (ltFunc w ti) ts
        in
        foldl' App (Var f) (as ++ as' ++ [e, e'])
    | t@(TyVar (Id n _)) <- typeOf e
    , Just f <- lookup n ti =
        App (App (Var f) e) e'
    | TyFun _ _ <- typeOf e =
        mkTrue kv tenv
    | t <- typeOf e
    ,  t == TyLitInt
    || t == TyLitDouble
    || t == TyLitFloat
    || t == TyLitChar =
        let
            lt = mkLt eenv
        in
        App (App (Prim Lt TyBottom) e) e'
    | otherwise = error $ "\nError in ltFuncCall" ++ show (typeOf e)

ltFunc :: Walkers -> [(Name, Id)] -> Type -> Expr
ltFunc _ ti tyvar@(TyVar (Id n _)) 
    | Just tyF <- lookup n ti = 
        Var tyF
ltFunc w _ t@(TyConApp n _)
    | Just f <- M.lookup n w =
       Var f

dataConName :: DataCon -> Name
dataConName (DataCon n _ _) = n


lhLeName :: Name -> Name
lhLeName (Name n _ _) = Name ("lhLeName" ++ n) Nothing 0

lhLeExpr :: Walkers -> Walkers -> ExprEnv -> Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
lhLeExpr ltW eqW eenv w (n, _) ng = 
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
lhGtName (Name n _ _) = Name ("lhGtName" ++ n) Nothing 0

lhGtExpr :: Walkers -> ExprEnv -> Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
lhGtExpr ltW eenv w (n, _) ng = 
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
lhGeName (Name n _ _) = Name ("lhGeName" ++ n) Nothing 0

lhGeExpr :: Walkers -> ExprEnv -> Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
lhGeExpr leW eenv w (n, _) ng = 
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
lhPolyPredName (Name n _ _) = Name ("lhPolyPred" ++ n) Nothing 0

lhPolyPred :: ExprEnv -> TypeEnv -> Name -> KnownValues -> Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
lhPolyPred eenv tenv lhTC kv w (n, adt) ng =
    let
        (adt', bni, wbni, ng2) = boundNameBindings lhTC adt ng
        bn = map idName bni

        tb = tyBool kv
        (fbi, ng3) = freshIds (map (\i -> TyFun (TyVar i) tb) bni) ng2

        bnf = zip bn fbi

        (e, ng4) = lhPolyPredCase eenv tenv kv w n adt' bn bnf ng3
    in
    (foldr Lam e (bni ++ fbi), ng4)

lhPolyPredCase :: ExprEnv -> TypeEnv -> KnownValues -> Walkers -> Name -> AlgDataTy -> [Name] -> [(Name, Id)] -> NameGen -> (Expr, NameGen)
lhPolyPredCase eenv tenv kv w n adt@(DataTyCon { data_cons = dc }) bn bnf ng =
    let
        t = TyConApp n $ map (TyVar . flip Id TYPE) bn

        (i1, ng2) = freshId t ng
        (caseB, ng3) = freshId t ng2

        (alts, ng4) = lhPolyPredAlts eenv tenv kv w dc bnf ng3

        c = Case (Var i1) caseB alts
    in
    (Lam i1 c, ng4)

lhPolyPredAlts :: ExprEnv -> TypeEnv -> KnownValues -> Walkers -> [DataCon] -> [(Name, Id)] -> NameGen -> ([Alt], NameGen)
lhPolyPredAlts _ _ _ _ [] _ ng = ([], ng)
lhPolyPredAlts eenv tenv kv w (dc@(DataCon _ _ ts):dcs) bnf ng =
    let
        (binds, ng2) = freshIds ts ng
        
        e = lhPolyPredCaseExpr eenv tenv kv w dc binds bnf

        alt = Alt (DataAlt dc binds) e

        (alts, ng3) = lhPolyPredAlts eenv tenv kv w dcs bnf ng2
    in
    (alt:alts, ng3)

lhPolyPredCaseExpr :: ExprEnv -> TypeEnv -> KnownValues -> Walkers-> DataCon -> [Id] -> [(Name, Id)] -> Expr
lhPolyPredCaseExpr eenv tenv kv w (DataCon n t ts) bn bnf =
    let
        tyvs = filter (isTyVar . typeOf) bn

        pc = map (predCalls bnf) tyvs 
    
        an = mkAnd eenv
        true = mkTrue kv tenv

        fs = map (polyPredFuncCall true w bnf) $ filter (not . isTyVar . typeOf) bn
    in
    foldr (\e -> App (App an e)) true $ pc ++ fs

predCalls :: [(Name, Id)] -> Id -> Expr
predCalls bnf i@(Id _ (TyVar tvi)) =
    let
        fi = lookup (idName tvi) bnf
    in
    case fi of
        Just fi' -> App (Var fi') (Var i)
        Nothing -> error $ "No function found in predCalls " ++ show i ++ "\n" ++ show bnf

polyPredFuncCall :: Expr -> Walkers -> [(Name, Id)] -> Id -> Expr
polyPredFuncCall true w bnf i
    | TyConApp n ts <- typeOf i
    , Just f <- M.lookup n w =
        let
            as = map Type ts
            as' = map (polyPredFunc w bnf) ts
        in
        foldl' App (Var f) (as ++ as' ++ [Var i])
    | TyFun _ _ <- typeOf i = true
    | t <- typeOf i
    ,  t == TyLitInt
    || t == TyLitDouble
    || t == TyLitFloat
    || t == TyLitChar = true
    | otherwise = error $ "Unhandled type " ++ show (typeOf i)

polyPredFunc :: Walkers -> [(Name, Id)] -> Type -> Expr
polyPredFunc _ bnf tyvar@(TyVar (Id n _)) 
    | Just tyF <- lookup n bnf = 
        Var tyF
polyPredFunc w _ t@(TyConApp n _)
    | Just f <- M.lookup n w =
        Var f
