module G2.Internals.Liquid.TCGen where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Liquid.TCValues

import Data.Coerce
import Data.Foldable
import qualified Data.Map as M
import Data.Maybe

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
        (tcn', ng2) = freshSeededName tcn ng

        (fn, ts, ws) = unzip3 ntws

        (dcN, ng3) = freshSeededName tcn ng2

        dc = DataCon dcN (mkTyFun (ts ++ [TyConApp dcN []])) ts

        adt = DataTyCon { bound_names = []
                        , data_cons = [dc] }

        tenv' = M.insert tcn' adt tenv

        -- Get type names
        ns = M.keys tenv'

        (eenv', ti, ng4) = genTCFuncs eenv tenv' [] ng3 dc ns ws

        tc' = coerce . M.insert tcn ti $ coerce tc
    in
    (eenv', tenv', tc', ng4)
genTC _ _ _ _ [] _ = error "No walkers given to genTC."

genTCFuncs :: ExprEnv -> TypeEnv -> [(Type, Id)] -> NameGen -> DataCon -> [Name] -> [Walkers] -> (ExprEnv, [(Type, Id)], NameGen)
genTCFuncs eenv tenv ti ng _ [] _ = (eenv, ti, ng)
genTCFuncs eenv tenv ti ng dc (n:ns) ws =
    let
        (fn, ng') = lhFuncName n ng

        t = M.lookup n tenv

        bn = case fmap bound_names t of
            Just bn' -> bn'
            Nothing -> error "Bound names not found in genTCFuncs"

        fs = mapMaybe (M.lookup n) ws

        e = mkApp $ Data dc:map Var fs

        eenv' = E.insert fn e eenv

        ti' = (TyConApp n [], Id fn (typeOf e)):ti
    in
    genTCFuncs eenv' tenv ti' ng' dc ns ws

lhFuncName :: Name -> NameGen -> (Name, NameGen)
lhFuncName (Name n _ _) ng = freshSeededString ("lh" ++ n ++ "Func") ng


createLHEq :: State -> (State, Walkers, TCValues)
createLHEq s@(State { expr_env = eenv
                    , type_env = tenv
                    , name_gen = ng
                    , known_values = kv
                    , type_classes = tc }) =
    let
        tenv' = M.toList tenv

        (eenv', ng2, eq_w) = createFuncs eenv ng tenv' M.empty (lhEqName . fst) lhStore (lhEqExpr tenv kv)
        (eenv'', ng3, neq_w) = createFuncs eenv' ng2 tenv' M.empty (lhNeqName . fst) lhStore (lhNeqExpr eq_w eenv')

        tb = tyBool kv

        ([lhTCN, lhEqN, lhNeN], ng4) = freshSeededStrings ["LH", "LHEq", "LHNe"] ng3

        (eenv''', tenv'', tc', ng5) = genTC eenv'' tenv tc lhTCN
                        [ (lhEqN, TyFun tb (TyFun tb tb), eq_w) 
                        , (lhNeN, TyFun tb (TyFun tb tb), neq_w)] ng4

        tcv = TCValues {lhTC = lhTCN, lhEq = lhEqN, lhNe = lhNeN}
    in
    (s { expr_env = eenv''', name_gen = ng5, type_env = tenv'', type_classes = tc' }, eq_w, tcv)

lhEqName :: Name -> Name
lhEqName (Name n _ _) = Name ("lhEqName" ++ n) Nothing 0


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

lhEqExpr :: TypeEnv -> KnownValues -> Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
lhEqExpr tenv kv w (n, adt) ng =
    let
        bn = bound_names adt

        -- Generates fresh names for TYPE variables, and eq function variables
        (bn', ng') = freshNames (length bn) ng
        (wbn, ng'') = freshNames (length bn) ng'

        bni = map (flip Id TYPE) bn'
        wbni = map (\(b, f) -> Id f 
            (TyFun 
                (TyVar (Id b TYPE))
                (TyFun
                    (TyVar (Id b TYPE))
                    (tyBool kv)
                )
            )) $ zip bn' wbn

        bfuncs = zip bn' wbni

        adt' = foldr (uncurry rename) adt (zip bn bn')

        (e, ng''') = lhEqCase tenv kv w bfuncs n bn' adt' ng''
    in
    (foldr Lam e (bni ++ wbni), ng''')

lhEqCase :: TypeEnv -> KnownValues -> Walkers -> [(Name, Id)] -> Name -> [Name] -> AlgDataTy -> NameGen -> (Expr, NameGen)
lhEqCase tenv kv w ti n bn adt@(DataTyCon {data_cons = dc}) ng =
    let
        t = TyConApp n $ map (TyVar . flip Id TYPE) bn

        (i1, ng2) = freshId t ng
        (caseB, ng3) = freshId t ng2

        (i2, ng4) = freshId t ng3

        (alts, ng5) = lhEqDataConAlts tenv kv w ti n caseB i2 bn  ng4 dc

        c = Case (Var i1) caseB alts
    in
    (Lam i1 (Lam i2 c), ng5)
lhEqCase tenv kv w ti _ bn (NewTyCon { rep_type = t@(TyConApp n _) }) ng =
    let
        t' = TyConApp n $ map (TyVar . flip Id TYPE) bn

        (i1, ng2) = freshId t ng
        (i2, ng3) = freshId t ng2

        v1 = Cast (Var i1) (t' :~ t)
        v2 = Cast (Var i2) (t' :~ t)

        e = eqFuncCall tenv kv w ti v1 v2
    in
    (Lam i1 (Lam i2 e), ng3)

lhEqDataConAlts :: TypeEnv -> KnownValues -> Walkers -> [(Name, Id)] -> Name -> Id -> Id -> [Name] -> NameGen -> [DataCon] -> ([Alt], NameGen)
lhEqDataConAlts _ _ _ _ _ _ _ _ ng [] = ([], ng)
lhEqDataConAlts tenv kv w ti n caseB1 i2 bn ng (dc@(DataCon dcn t ts):xs) =
    let
        (binds1, ng2) = freshIds ts ng

        (caseB2, ng3) = freshId t ng2

        (cAlts, ng4) = lhEqCase2Alts tenv kv w ti caseB1 caseB2 binds1 dc ng3

        c = Case (Var i2) caseB2 cAlts
            
        alt = Alt (DataAlt dc binds1) c

        (alts, ng5) = lhEqDataConAlts tenv kv w ti n caseB1 i2 bn ng4 xs
    in
    (alt:alts, ng5)

lhEqCase2Alts :: TypeEnv -> KnownValues -> Walkers -> [(Name, Id)] -> Id -> Id -> [Id] -> DataCon -> NameGen -> ([Alt], NameGen)
lhEqCase2Alts tenv kv w ti caseB1 caseB2 binds1 dc@(DataCon dcn t ts) ng =
 let
    (binds2, ng2) = freshIds ts ng

    t = tyBool kv
    true = mkTrue kv tenv
    false = mkFalse kv tenv

    -- Check that the two DataCons args are equal
    zbinds = zip (map Var binds1) (map Var binds2)

    e = foldr (\e -> App (App (Prim And TyBottom) e)) true
      $ map (uncurry (eqFuncCall tenv kv w ti)) zbinds
 in
 ([ Alt (DataAlt dc binds2) e
  , Alt Default false ]
 , ng2)

eqFuncCall :: TypeEnv -> KnownValues ->  Walkers -> [(Name, Id)] -> Expr -> Expr -> Expr
eqFuncCall tenv kv w ti e e'
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
    || t == TyLitChar = App (App (Prim Eq TyBottom) e) e'
    | otherwise = error $ "\nError in eqFuncCall" ++ show (typeOf e)

eqFunc :: Walkers -> [(Name, Id)] -> Type -> Expr
eqFunc _ ti tyvar@(TyVar (Id n _)) 
    | Just tyF <- lookup n ti = 
        Var tyF
eqFunc w _ t@(TyConApp n _)
    | Just f <- M.lookup n w =
       Var f


lhNeqName :: Name -> Name
lhNeqName (Name n _ _) = Name ("lhNeqName" ++ n) Nothing 0

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

        (li', ng') = freshIds (map typeOf li) ng
        e = foldr Lam (App (Prim Not TyBottom) (Var f)) li'
    in
    (e, ng')