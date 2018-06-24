{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Initialization.StructuralEq (createStructEqFuncs) where

import qualified G2.Internals.Initialization.Types as IT
import G2.Internals.Language
import G2.Internals.Language.Monad
import G2.Internals.Language.KnownValues

import Data.Coerce
import qualified Data.Foldable as F
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

-- | createStructEqFuncs
-- Creates a typeclass to compare two ADTs based on there structural equality-
-- that is, compare if they have exactly the same (possibly recursive) constructors.
-- If some of the constructors have higher order function arguments,
-- those higher order functions are not checked for equality, and do not prevent
-- the overall ADTs from being called structurally equal.
-- Returns the name of the typeclass, and the function that checks for structural equality. 
createStructEqFuncs :: [Type] -> IT.SimpleStateM ()
createStructEqFuncs ts = do
    -- Create a name for the new type class, adt, and datacon
    tcn <- freshSeededStringN "structEq"
    adtn <- freshSeededStringN "structEq"
    dcn <- freshSeededStringN "structEq"

    let t = TyConApp tcn []

    tyvn <- freshSeededStringN "a"
    let tyvn' = TyVar (Id tyvn TYPE)
    tb <- tyBoolT

    let dc = DataCon dcn (TyFun (TyFun tyvn' (TyFun tyvn' tb)) t) [tyvn']

    ex <- genExtractor t dc

    -- Update KnownValues
    kv <- knownValues
    let kv' = kv { structEqTC = tcn, structEqFunc = ex }
    IT.putKnownValues kv'

    tenv <- typeEnv
    -- For efficiency, we only generate structural equality when it's needed
    let types = mapMaybe (tcaName . returnType) $ filter isTyFun ts ++ (nubBy (.::.) $ argTypesTEnv tenv)
    let tenv' = M.filterWithKey (\n _ -> n `elem` types) tenv

    insertT adtn (DataTyCon {bound_names = [], data_cons = [dc]})

    let (tenvK, tenvV) = unzip $ M.toList tenv'

    -- Create names for the new functions
    let ns = map (\(Name n _ _ _) -> Name ("structEq" `T.append` n) Nothing 0 Nothing) tenvK
    ns' <- freshSeededNamesN ns
    let nsT = zip tenvK $ map (flip Id (TyConApp tcn [])) ns'

    tc <- IT.typeClasses
    tci <- freshIdN TYPE

    ins <- genInsts tcn nsT t dc $ M.toList tenv'

    let tc' = coerce . M.insert tcn (Class { insts = ins, typ_ids = [tci] }) $ coerce tc
    IT.putTypeClasses tc'

    F.mapM_ (\(n, n', adt) -> createStructEqFunc dcn n n' adt) $ zip3 ns' tenvK tenvV

tcaName :: Type -> Maybe Name
tcaName (TyConApp n _) = Just n
tcaName _ = Nothing

genExtractor :: Type -> DataCon  -> IT.SimpleStateM Name
genExtractor t dc = do
    lami <- freshIdN t
    ci <- freshIdN t

    tb <- tyBoolT
    tyvn <- freshSeededStringN "a"
    let tyvn' = TyVar (Id tyvn TYPE)
    fi <- freshIdN $ TyFun tyvn' (TyFun tyvn' tb)

    let alt = Alt (DataAlt dc [fi]) $ Var fi
    let e = Lam (Id tyvn TYPE) $ Lam lami $ Case (Var lami) ci $ [alt]

    extractN <- freshSeededStringN "structEq"

    insertE extractN e

    return extractN


genInsts :: Name -> [(Name, Id)] -> Type -> DataCon -> [(Name, AlgDataTy)] -> IT.SimpleStateM [(Type, Id)]
genInsts _ _ _ _ [] = return []
genInsts tcn nsT t dc ((n@(Name n' _ _ _), adt):xs) = do
    let bn = bound_names adt
    bn' <- freshSeededNamesN bn

    let bni = map (flip Id TYPE) bn
        bnid = map (\(dni, i) -> Id dni (TyConApp tcn [TyVar i])) $ zip bn' bni
        
        -- Make the expressions
        bnv = map TyVar bni
        tbnv = map Type bnv
        dv = map Var bnid

        eqfn = case lookup n nsT of
                Just f -> f
                Nothing -> error "No name found in genInsts"

        vs = mkApp (Var eqfn:tbnv ++ dv)

        e = mkLams (bni ++ bnid) $ App (Data dc) vs

    dn <- freshSeededNameN (Name ("structEqDict" `T.append` n') Nothing 0 Nothing)
    insertE dn e

    xs' <- genInsts tcn nsT t dc xs

    return $ (TyConApp n bnv, Id dn t):xs'


createStructEqFunc :: Name -> Name -> Name -> AlgDataTy -> IT.SimpleStateM ()
createStructEqFunc dcn fn tn (DataTyCon {bound_names = ns, data_cons = dc}) = do
    ns' <- freshSeededNamesN ns
    let t = TyConApp tn (map (TyVar . flip Id TYPE) ns')

    bt <- freshIdsN $ map (const TYPE) ns
    bd <- freshIdsN $ map (\i -> TyConApp dcn [TyVar i]) bt

    let bm = zip (map idName bt) $ zip bt bd

    let dc' = foldr (\(n, rt) -> retype (Id n TYPE) rt) dc $ zip ns (map TyVar bt)

    e <- createStructEqFuncDC t bt bd bm dc'
    insertE fn e
    -- kv <- knownValues
    -- tc <- IT.typeClasses
    -- let eq = case eqTCDict kv tc (TyConApp tn []) of
    --             Just i -> i
    --             Nothing -> Id (Name "BAD" Nothing 0 Nothing) TyBottom
    -- let eqf = eqFunc kv

    -- insertE fn (App (App (Var (Id eqf TyUnknown)) (Type (TyConApp tn []))) (Var eq))
createStructEqFunc dcn fn tn (NewTyCon {bound_names = ns, data_con = dc, rep_type = rt}) = do
    kv <- knownValues
    tc <- IT.typeClasses
    let sef = structEqTCDict kv tc rt

    return ()
createStructEqFunc _ _ _ (TypeSynonym {}) = error "Type synonym in createStructEqFunc"

createStructEqFuncDC :: Type -> [Id] -> [Id] -> [(Name, (Id, Id))] -> [DataCon] -> IT.SimpleStateM Expr
createStructEqFuncDC t bt bd bm dc = do
    lam1I <- freshIdN t
    lam2I <- freshIdN t

    b1 <- freshIdN t

    alts <- mapM (createStructEqFuncDCAlt (Var b1) (Var lam2I) t bm) dc

    let e = Lam lam1I $ Lam lam2I $ Case (Var lam1I) b1 alts
    let e' = foldr Lam e bd
    return $ foldr Lam e' bt

createStructEqFuncDCAlt :: Expr -> Expr -> Type -> [(Name, (Id, Id))] ->  DataCon -> IT.SimpleStateM Alt
createStructEqFuncDCAlt e1 e2 t bm dc@(DataCon _ _ ts) = do
    true <- mkTrueE
    false <- mkFalseE

    b <- freshIdN t
    bs <- freshIdsN ts

    b2 <- freshIdN t
    bs2 <- freshIdsN ts

    sEqCheck <- boundChecks t bs bs2 bm

    let alt2 = Alt (DataAlt dc bs2) sEqCheck
    let altD = Alt Default false

    return $ Alt (DataAlt dc bs) (Case e2 b2 [alt2, altD])

boundChecks :: Type -> [Id] -> [Id] -> [(Name, (Id, Id))] -> IT.SimpleStateM Expr
boundChecks t is1 is2 bm = do
    and <- mkAndE
    true <- mkTrueE

    bc <- mapM (uncurry (boundCheck bm)) $ zip is1 is2

    return $ foldr (\e -> App (App and e)) true bc

boundCheck :: [(Name, (Id, Id))] -> Id -> Id -> IT.SimpleStateM Expr
boundCheck bm i1 i2 = do
    structEqCheck bm (typeOf i1) i1 i2

structEqCheck :: [(Name, (Id, Id))] -> Type -> Id -> Id -> IT.SimpleStateM Expr
structEqCheck bm t@(TyConApp n ts) i1 i2 = do
    kv <- knownValues
    tc <- IT.typeClasses

    let ex = Var $ Id (structEqFunc kv) TyUnknown

    dict <- dictForType bm t
    -- let dict = case structEqTCDict kv tc t of
    --                 Just i -> foldr App (Var i) tsD
    --                 Nothing -> error $ "Required typeclass not found in structEqCheck"
    return (App (App (App (App ex (Type t)) dict) (Var i1)) (Var i2))
structEqCheck bm (TyVar (Id n _)) (Id n' _) (Id n'' _) = do
    kv <- knownValues

    case lookup n bm of
        Just (ty, dict) -> do
            let ex = Var $ Id (structEqFunc kv) TyUnknown

            return (App (App (App (App ex (Var ty)) (Var dict)) (Var (Id n' (TyVar ty)))) (Var (Id n'' (TyVar ty))))
        Nothing -> error "Unaccounted for TyVar in structEqCheck"
structEqCheck _ TyLitInt i1 i2 = return $ App (App (Prim Eq TyUnknown) (Var i1)) (Var i2)
structEqCheck _ TyLitFloat i1 i2 = return $ App (App (Prim Eq TyUnknown) (Var i1)) (Var i2)
structEqCheck _ TyLitDouble i1 i2 = return $ App (App (Prim Eq TyUnknown) (Var i1)) (Var i2)
structEqCheck _ TyLitChar i1 i2 = return $ App (App (Prim Eq TyUnknown) (Var i1)) (Var i2)
structEqCheck _ (TyForAll _ _) _ _ = mkTrueE
structEqCheck _ (TyFun _ _) _ _ = mkTrueE
structEqCheck _ t _ _ = error $ "Unsupported type in structEqCheck" ++ show t

dictForType :: [(Name, (Id, Id))] -> Type -> IT.SimpleStateM Expr
dictForType bm t@(TyConApp n ts) = do
    kv <- knownValues
    tc <- IT.typeClasses

    ds <- mapM (dictForType bm) ts

    case structEqTCDict kv tc t of
        Just i -> return $ foldl' App (Var i) (map Type ts ++ ds)
        Nothing -> error $ "Required typeclass not found in dictForType"
dictForType bm (TyVar (Id n _)) =
    case lookup n bm of
        Just (_, dict) -> return (Var dict)
        Nothing -> error "Unaccounted for TyVar in dictForType"
dictForType _ t = error $ "Unsupported type in dictForType" ++ show t
