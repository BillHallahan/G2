{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Initialization.StructuralEq (createStructEqFuncs) where

import qualified G2.Initialization.Types as IT
import G2.Language
import G2.Language.Monad
import G2.Language.KnownValues

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

    let t = TyCon tcn TYPE

    tyvn <- freshSeededStringN "a"
    let tyvn' = TyVar (Id tyvn TYPE)
    tb <- tyBoolT

    let dc = DataCon dcn (TyFun (TyFun tyvn' (TyFun tyvn' tb)) t)

    ex <- genExtractor t dc

    -- Update KnownValues
    kv <- knownValues
    let kv' = kv { structEqTC = tcn, structEqFunc = ex }
    IT.putKnownValues kv'

    tenv <- typeEnv
    -- For efficiency, we only generate structural equality when it's needed
    let types = mapMaybe (tcaName . returnType . PresType) $ filter isTyFun ts ++ (nubBy (.::.) $ argTypesTEnv tenv)
    let tenv' = M.filterWithKey (\n _ -> n `elem` types) tenv

    insertT adtn (DataTyCon {bound_ids = [Id tyvn TYPE], data_cons = [dc]})

    let (tenvK, tenvV) = unzip $ M.toList tenv'

    -- Create names for the new functions
    let ns = map (\(Name n _ _ _) -> Name ("structEq" `T.append` n) Nothing 0 Nothing) tenvK
    ns' <- freshSeededNamesN ns
    let nsT = zip tenvK $ map (flip Id (TyCon tcn TYPE)) ns'

    tc <- IT.typeClasses
    tci <- freshIdN TYPE

    ins <- genInsts tcn nsT t dc $ M.toList tenv'

    let tc' = coerce . M.insert tcn (Class { insts = ins, typ_ids = [tci] }) $ coerce tc
    IT.putTypeClasses tc'

    F.mapM_ (\(n, n', adt) -> createStructEqFunc dcn n n' adt) $ zip3 ns' tenvK tenvV

tcaName :: Type -> Maybe Name
tcaName (TyCon n _) = Just n
tcaName (TyApp t _) = tcaName t
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
    let e = Lam TypeL (Id tyvn TYPE) $ Lam TermL lami $ Case (Var lami) ci $ [alt]

    extractN <- freshSeededStringN "structEq"

    insertE extractN e

    return extractN


genInsts :: Name -> [(Name, Id)] -> Type -> DataCon -> [(Name, AlgDataTy)] -> IT.SimpleStateM [(Type, Id)]
genInsts _ _ _ _ [] = return []
genInsts tcn nsT t dc ((n@(Name n' _ _ _), adt):xs) = do
    let bn = map idName $ bound_ids adt
    bn' <- freshSeededNamesN bn

    let bni = map (flip Id TYPE) bn
        bnid = map (\(dni, i) -> Id dni (TyApp (TyCon tcn (TyFun TYPE TYPE)) (TyVar i))) $ zip bn' bni
        
        -- Make the expressions
        bnv = map TyVar bni
        bnvK = mkTyApp $ map (const TYPE) bnv
        tbnv = map Type bnv
        dv = map Var bnid

        eqfn = case lookup n nsT of
                Just f -> f
                Nothing -> error "No name found in genInsts"

        vs = mkApp (Var eqfn:tbnv ++ dv)

        e = mkLams (map (TypeL,) bni ++ map (TermL,) bnid) $ App (Data dc) vs

    dn <- freshSeededNameN (Name ("structEqDict" `T.append` n') Nothing 0 Nothing)
    insertE dn e

    xs' <- genInsts tcn nsT t dc xs

    return $ (mkTyApp (TyCon n bnvK:bnv), Id dn t):xs'


createStructEqFunc :: Name -> Name -> Name -> AlgDataTy -> IT.SimpleStateM ()
createStructEqFunc dcn fn tn (DataTyCon {bound_ids = ns, data_cons = dc}) = do
    ns' <- freshSeededNamesN $ map idName ns
    let t = mkFullAppedTyCon tn (map (TyVar . flip Id TYPE) ns') TYPE

    bt <- freshIdsN $ map (const TYPE) ns
    bd <- freshIdsN $ map (\i -> TyApp (TyCon dcn (TyFun TYPE TYPE)) (TyVar i)) bt

    let bm = zip (map idName bt) $ zip bt bd

    let dc' = foldr (\(i, rt) -> retype i rt) dc $ zip ns (map TyVar bt)

    e <- createStructEqFuncDC t bt bd bm dc'
    insertE fn e
createStructEqFunc dcn fn tn (NewTyCon {bound_ids = ns, rep_type = rt}) = do
    kv <- knownValues

    let t = mkFullAppedTyCon tn (map TyVar ns) TYPE

    bt <- freshIdsN $ map typeOf ns
    bd <- freshIdsN $ map (\i -> TyApp (TyCon dcn (TyFun TYPE TYPE)) (TyVar i)) bt
    let bm = zip (map idName bt) $ zip bt bd

    let t' = foldr (\(i, t_) -> retype i t_) t $ zip ns (map TyVar bt)

    lam1I <- freshIdN t'
    lam2I <- freshIdN t'

    let rt' = foldr (\(i, rt_) -> retype i rt_) rt $ zip ns (map TyVar bt)
    d <- dictForType bm rt'

    let ex = Var $ Id (structEqFunc kv) $ TyFun (typeOf (Type rt')) $ TyFun (typeOf d) $ TyFun t' $ TyFun t' t
    let c = t' :~ rt'
    let cLam1I = Cast (Var lam1I) c
    let cLam2I = Cast (Var lam2I) c


    let e = Lam TermL lam1I $ Lam TermL lam2I $ App (App (App (App ex (Type rt')) d) cLam1I) cLam2I
    let e' = mkLams (map (TermL,) bd) e
    let e'' = mkLams (map (TypeL,) bt) e'

    insertE fn e''
createStructEqFunc _ _ _ (TypeSynonym {}) = error "Type synonym in createStructEqFunc"

createStructEqFuncDC :: Type -> [Id] -> [Id] -> [(Name, (Id, Id))] -> [DataCon] -> IT.SimpleStateM Expr
createStructEqFuncDC t bt bd bm dc = do
    lam1I <- freshIdN t
    lam2I <- freshIdN t

    b1 <- freshIdN t

    alts <- mapM (createStructEqFuncDCAlt (Var lam2I) t bm) dc

    let e = Lam TermL lam1I $ Lam TermL lam2I $ Case (Var lam1I) b1 alts
    let e' = mkLams (map (TermL,) bd) e
    return $ mkLams (map (TypeL,) bt) e'

createStructEqFuncDCAlt :: Expr -> Type -> [(Name, (Id, Id))] ->  DataCon -> IT.SimpleStateM Alt
createStructEqFuncDCAlt e2 t bm dc@(DataCon _ _) = do
    false <- mkFalseE

    bs <- freshIdsN $ anonArgumentTypes dc

    b <- freshIdN t
    bs2 <- freshIdsN $ anonArgumentTypes dc

    sEqCheck <- boundChecks bs bs2 bm

    let alt2 = Alt (DataAlt dc bs2) sEqCheck
    let altD = Alt Default false

    return $ Alt (DataAlt dc bs) (Case e2 b [alt2, altD])

boundChecks :: [Id] -> [Id] -> [(Name, (Id, Id))] -> IT.SimpleStateM Expr
boundChecks is1 is2 bm = do
    andE <- mkAndE
    true <- mkTrueE

    bc <- mapM (uncurry (boundCheck bm)) $ zip is1 is2

    return $ foldr (\e -> App (App andE e)) true bc

boundCheck :: [(Name, (Id, Id))] -> Id -> Id -> IT.SimpleStateM Expr
boundCheck bm i1 i2 = do
    structEqCheck bm (typeOf i1) i1 i2

structEqCheck :: [(Name, (Id, Id))] -> Type -> Id -> Id -> IT.SimpleStateM Expr
structEqCheck bm t i1 i2
    | TyCon _ _ <- tyAppCenter t = do
    kv <- knownValues

    let ex = Var $ Id (structEqFunc kv) TyUnknown

    dict <- dictForType bm t

    return (App (App (App (App ex (Type t)) dict) (Var i1)) (Var i2))
structEqCheck bm (TyVar (Id n _)) (Id n' _) (Id n'' _) = do
    kv <- knownValues

    case lookup n bm of
        Just (ty, dict) -> do
            let ex = Var $ Id (structEqFunc kv) TyUnknown

            return (App (App (App (App ex (Var ty)) (Var dict)) (Var (Id n' (TyVar ty)))) (Var (Id n'' (TyVar ty))))
        Nothing -> error "Unaccounted for TyVar in structEqCheck"
structEqCheck _ TyLitInt i1 i2 = do
    eq <- mkEqPrimIntE
    return $ App (App eq (Var i1)) (Var i2)
structEqCheck _ TyLitFloat i1 i2 = do
    eq <- mkEqPrimFloatE
    return $ App (App eq (Var i1)) (Var i2)
structEqCheck _ TyLitDouble i1 i2 = do
    eq <- mkEqPrimDoubleE
    return $ App (App eq (Var i1)) (Var i2)
structEqCheck _ TyLitChar i1 i2 = do
    eq <- mkEqPrimCharE
    return $ App (App eq (Var i1)) (Var i2)
structEqCheck _ (TyForAll _ _) _ _ = mkTrueE
structEqCheck _ (TyFun _ _) i1 i2 = return $ App (App (Prim BindFunc TyUnknown) (Var i1)) (Var i2) -- mkTrueE
structEqCheck _ t _ _ = error $ "Unsupported type in structEqCheck" ++ show t

dictForType :: [(Name, (Id, Id))] -> Type -> IT.SimpleStateM Expr
dictForType bm t
    | TyCon _ _ <- tyAppCenter t
    , ts <- tyAppArgs t = do
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
