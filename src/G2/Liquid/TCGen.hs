{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
module G2.Liquid.TCGen (createLHState) where

import G2.Language
import qualified G2.Language.KnownValues as KV
import G2.Language.Monad
import G2.Liquid.Conversion
import G2.Liquid.TCValues
import G2.Liquid.Types

import Data.Foldable
import qualified Data.Map as M
import qualified Data.Text as T

-- | Creates an LHState.  This involves building a TCValue, and
-- creating the new LH TC which checks equality, and has a function to
-- check refinements of polymorphic types
createLHState :: Measures -> KnownValues -> State [FuncCall] -> Bindings -> (LHState, Bindings)
createLHState meenv mkv s b =
    let
        (tcv, (s', b')) = runStateM (createTCValues mkv) s b

        lh_s = consLHState s' meenv tcv
    in
    execLHStateM (do
                    createLHTCFuncs
                    createExtractors) lh_s b'
    

createTCValues :: KnownValues -> StateM [FuncCall] TCValues
createTCValues kv = do
    lhTCN <- freshSeededStringN "lh"
    lhEqN <- freshSeededStringN "lhEq"
    lhNeN <- freshSeededStringN "lhNe"

    lhLtN <- freshSeededStringN "lhLt"
    lhLeN <- freshSeededStringN "lhLe"
    lhGtN <- freshSeededStringN "lhGt"
    lhGeN <- freshSeededStringN "lhGe"

    lhPPN <- freshSeededStringN "lhPP"
    lhNuOr <- freshSeededStringN "lhNuOr"

    let tcv = (TCValues { lhTC = lhTCN
                        , lhNumTC = KV.numTC kv 
                        , lhOrdTC = KV.ordTC kv 

                        , lhEq = lhEqN
                        , lhNe = lhNeN
                        , lhLt = lhLtN
                        , lhLe = lhLeN
                        , lhGt = lhGtN
                        , lhGe = lhGeN

                        , lhPlus = KV.plusFunc kv
                        , lhMinus = KV.minusFunc kv
                        , lhTimes = KV.timesFunc kv
                        , lhDiv = KV.divFunc kv
                        , lhNegate = KV.negateFunc kv
                        , lhMod = KV.modFunc kv
                        , lhFromInteger = KV.fromIntegerFunc kv
                        , lhNumOrd = lhNuOr

                        , lhAnd = KV.andFunc kv
                        , lhOr = KV.orFunc kv

                        , lhPP = lhPPN })

    return tcv

type PredFunc = LHDictMap -> Name -> AlgDataTy -> DataCon -> [Id] -> LHStateM [Alt]

createLHTCFuncs :: LHStateM ()
createLHTCFuncs = do
    lhm <- mapM (uncurry initalizeLHTC) . M.toList =<< typeEnv
    let lhm' = M.fromList lhm

    -- createLHTCFuncs' relies on the standard TypeClass lookup functions to get access to
    -- LH Dicts.  So it is important that, before calling it, we set up the TypeClass correctly
    lhtc <- mapM (\(n, f) -> do
                                adt <- lookupT n
                                case adt of
                                    Just adt' -> do
                                        let bnvK = mkTyApp $ map (const TYPE) $ bound_ids adt'
                                        return (TyCon n bnvK, f)
                                    Nothing -> error $ "No LH Dict name for " ++ show n) lhm

    tc <- typeClasses
    tcn <- lhTCM
    tci <- freshIdN TYPE
    let tc' = insertClass tcn (Class { insts = lhtc, typ_ids = [tci] }) tc
    putTypeClasses tc'

    -- Now, we do the work of actually generating all the code/functions for the typeclass
    mapM_ (uncurry (createLHTCFuncs' lhm')) . M.toList =<< typeEnv

initalizeLHTC :: Name -> AlgDataTy -> LHStateM (Name, Id)
initalizeLHTC n adt = do
    lhf <- lhName "lh" n
    t <- lhtcT n adt
    return (n, Id lhf t)

lhtcT :: Name -> AlgDataTy -> LHStateM Type
lhtcT n adt = do
    lh <- lhTCM
    let bi = bound_ids adt
    let ct = foldl' TyApp (TyCon n TYPE) $ map TyVar bi

    let t = (TyApp 
                (TyCon lh TYPE) 
                ct
            )

    let t' = foldr TyFun t $ map (TyApp (TyCon lh (TyFun TYPE TYPE)) . TyVar) bi
    let t'' = foldr TyForAll t' $ map NamedTyBndr bi
    return t''

lhName :: T.Text -> Name -> LHStateM Name
lhName t (Name n m _ _) = freshSeededNameN $ Name (t `T.append` n) m 0 Nothing

createLHTCFuncs' :: LHDictMap -> Name -> AlgDataTy -> LHStateM ()
createLHTCFuncs' lhm n adt = do
    eqN <- lhName "lhEq" n
    eq <- createFunc lhEqFunc n adt
    insertMeasureM eqN eq

    neN <- lhName "lhNe" n
    ne <- createFunc lhNeFunc n adt
    insertMeasureM neN ne

    ltN <- lhName "lhLt" n
    lt <- createLtFunc n adt
    insertMeasureM ltN lt

    leN <- lhName "lhLe" n
    le <- createLeFunc n adt
    insertMeasureM leN le

    gtN <- lhName "lhGt" n
    gt <- createGtFunc n adt
    insertMeasureM gtN gt

    geN <- lhName "lhGe" n
    ge <- createGeFunc n adt
    insertMeasureM geN ge

    ppN <- lhName "lhPP" n
    pp <- lhPPFunc n adt
    insertMeasureM ppN pp

    -- We define a function to get the LH Dict for this type
    -- It takes and passes on the type arguments, and the LH Dicts for those
    -- type arguments
    lh <- lhTCM

    let bi = bound_ids adt
    let bt = map (Type . TyVar) bi
    lhd <- freshIdsN (map (TyApp (TyCon lh (TyApp TYPE TYPE)) . TyVar) bi)
    let lhdv = map Var lhd


    let fs = map (\(n', t) -> Var (Id n' t)) [ (eqN, (typeOf eq))
                                           , (neN, (typeOf ne))
                                           , (ltN, (typeOf lt))
                                           , (leN, (typeOf le))
                                           , (gtN, (typeOf gt))
                                           , (geN, (typeOf ge))
                                           , (ppN, (typeOf pp)) ]
    let fs' = map (\f -> mkApp $ f:bt ++ lhdv) fs

    lhdct <- lhDCType
    let e = mkApp $ Data (DataCon lh lhdct):fs'
    let e' = foldr (Lam TermL) e lhd
    let e'' = foldr (Lam TypeL) e' bi

    let fn = M.lookup n lhm

    case fn of
        Just fn' -> do
            insertMeasureM (idName fn') e''
            -- let bnvK = mkTyApp $ map (const TYPE) bi
            return () -- return (TyCon n bnvK, fn')
        Nothing -> error $ "No LH Dict name for " ++ show n


lhDCType :: LHStateM Type
lhDCType = do
    lh <- lhTCM
    n <- freshIdN TYPE

    a <- freshSeededStringN "a"
    bool <- tyBoolT
    let tva = TyVar (Id a TYPE)
    let taab = TyFun tva (TyFun tva bool)


    return $ (TyFun
                taab -- eq
                (TyFun
                    taab --neq
                    (TyFun
                        taab --lt
                        (TyFun
                            taab --le
                            (TyFun
                                taab --gt
                                (TyFun
                                    taab --ge
                                    (TyFun
                                        TyUnknown
                                        (TyApp 
                                            (TyCon lh TYPE) 
                                            (TyVar n)
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )

createFunc :: PredFunc -> Name -> AlgDataTy -> LHStateM Expr 
createFunc cf n adt = do
    -- Our function needs the following arguments:
    -- Type arguments
    -- A LH typeclass for each type argument
    -- Two expression of the adt type
    -- We set up the needed Ids here
    let bi = bound_ids adt

    lh <- lhTCM
    lhbi <- mapM (freshIdN . TyApp (TyCon lh TYPE) . TyVar) bi

    d1 <- freshIdN (TyCon n TYPE)
    d2 <- freshIdN (TyCon n TYPE)

    let m = M.fromList $ zip (map idName bi) lhbi
    e <- mkFirstCase cf m d1 d2 n adt

    let e' = mkLams (map (TypeL,) bi ++ map (TermL,) lhbi ++ [(TermL, d1), (TermL, d2)]) e

    return e'

mkFirstCase :: PredFunc -> LHDictMap -> Id -> Id -> Name -> AlgDataTy -> LHStateM Expr
mkFirstCase f ldm d1 d2 n adt@(DataTyCon { data_cons = dcs }) = do
    caseB <- freshIdN (typeOf d1)
    return . Case (Var d1) caseB =<< mapM (mkFirstCase' f ldm d2 n adt) dcs
mkFirstCase _ _ _ _ _ _ = return $ Var (Id (Name "Bad mkFirstCase" Nothing 0 Nothing) TyUnknown)

mkFirstCase' :: PredFunc -> LHDictMap -> Id -> Name -> AlgDataTy -> DataCon -> LHStateM Alt
mkFirstCase' f ldm d2 n adt dc = do
    ba <- freshIdsN $ anonArgumentTypes dc

    return . Alt (DataAlt dc ba) =<< mkSecondCase f ldm d2 n adt dc ba

mkSecondCase :: PredFunc -> LHDictMap -> Id -> Name -> AlgDataTy -> DataCon -> [Id] -> LHStateM Expr
mkSecondCase f ldm d2 n adt dc ba1 = do
    caseB <- freshIdN (typeOf dc)

    alts <- f ldm n adt dc ba1

    return $ Case (Var d2) caseB alts

lhEqFunc :: PredFunc
lhEqFunc ldm _ _ dc ba1 = do
    ba2 <- freshIdsN $ anonArgumentTypes dc

    an <- lhAndE
    true <- mkTrueE
    false <- mkFalseE

    pr <- mapM (uncurry (eqLHFuncCall ldm)) $ zip ba1 ba2
    let pr' = foldr (\e -> App (App an e)) true pr

    return [ Alt Default false
           , Alt (DataAlt dc ba2) pr'] 

eqLHFuncCall :: LHDictMap -> Id -> Id -> LHStateM Expr
eqLHFuncCall ldm i1 i2
    | TyCon _ _ <- tyAppCenter t = do
        lhe <- lhEqM

        i <- freshIdN TYPE
        b <- tyBoolT

        let lhv = App (Var $ Id lhe (TyForAll (NamedTyBndr i) (TyFun (TyVar i) (TyFun (TyVar i) b)))) (Type t)
        lhd <- lhTCDict' ldm t

        return $ foldl' App (App lhv lhd) [Var i1, Var i2]

    | TyVar _ <- t = do
        lhe <- lhEqM

        i <- freshIdN TYPE
        b <- tyBoolT

        lhd <- lhTCDict' ldm t

        let lhv = App (Var (Id lhe (TyForAll (NamedTyBndr i) (TyFun (TyVar i) (TyFun (TyVar i) b))))) (Type t)
        return $ App (App (App lhv lhd) (Var i1)) (Var i2)

    | TyFun _ _ <- t = mkTrueE
    | TyForAll _ _ <- t = mkTrueE
    
    |  t == TyLitInt
    || t == TyLitDouble
    || t == TyLitFloat
    || t == TyLitChar = do
        b <- tyBoolT
        let pt = TyFun t (TyFun t b)
        
        return $ App (App (Prim Eq pt) (Var i1)) (Var i2)

    | otherwise = error $ "\nError in eqLHFuncCall " ++ show t ++ "\n" ++ show ldm
    where
        t = typeOf i1

lhNeFunc :: PredFunc
lhNeFunc ldm _ _ dc ba1 = do
    ba2 <- freshIdsN $ anonArgumentTypes dc

    an <- lhAndE
    true <- mkTrueE
    false <- mkFalseE

    trueDC <- mkDCTrueM
    falseDC <- mkDCFalseM

    pr <- mapM (uncurry (eqLHFuncCall ldm)) $ zip ba1 ba2
    let pr' = foldr (\e -> App (App an e)) true pr

    b <- freshIdN =<< tyBoolT
    let pr'' = Case pr' b [ Alt (DataAlt trueDC []) false
                          , Alt (DataAlt falseDC []) true ]

    return [ Alt Default false
           , Alt (DataAlt dc ba2) pr''] 

createLtFunc :: Name -> AlgDataTy -> LHStateM Expr
createLtFunc = createOrdFunc Lt

createLeFunc :: Name -> AlgDataTy -> LHStateM Expr
createLeFunc = createOrdFunc Le

createGtFunc :: Name -> AlgDataTy -> LHStateM Expr
createGtFunc = createOrdFunc Gt

createGeFunc :: Name -> AlgDataTy -> LHStateM Expr
createGeFunc = createOrdFunc Ge

-- We currently treat relations between Ints/Floats/Doubles correctly,
-- and just assume all other relations are true.
-- In LH, relations between x :: T and y :: T work by checking that
--    f x < f y
-- for all f :: T -> Int, so this could make us miss some counterexamples.
-- However, we will never generate an incorrect counterexample.
-- (i.e. it is sound but incomplete)
createOrdFunc :: Primitive -> Name -> AlgDataTy -> LHStateM Expr 
createOrdFunc pr n adt = do
    let bi = bound_ids adt

    lh <- lhTCM
    lhbi <- mapM (freshIdN . TyApp (TyCon lh TYPE) . TyVar) bi

    d1 <- freshIdN (TyCon n TYPE)
    d2 <- freshIdN (TyCon n TYPE)

    kv <- knownValues
    e <- mkOrdCases pr kv d1 d2 n adt

    let e' = mkLams (map (TypeL,) bi ++ map (TermL,) lhbi ++ [(TermL, d1), (TermL, d2)]) e

    return e'

mkOrdCases :: Primitive -> KnownValues -> Id -> Id -> Name -> AlgDataTy -> LHStateM Expr
mkOrdCases pr kv i1 i2 n (DataTyCon { data_cons = [dc]})
    | n == KV.tyInt kv = mkPrimOrdCases pr TyLitInt i1 i2 dc
    | n == KV.tyFloat kv = mkPrimOrdCases pr TyLitFloat i1 i2 dc
    | n == KV.tyDouble kv = mkPrimOrdCases pr TyLitDouble i1 i2 dc
    | otherwise = mkTrueE
mkOrdCases _ _ _ _ _ _ = mkTrueE

mkPrimOrdCases :: Primitive -> Type -> Id -> Id -> DataCon -> LHStateM Expr
mkPrimOrdCases pr t i1 i2 dc = do
    i1' <- freshIdN (typeOf dc)
    i2' <- freshIdN (typeOf dc)

    b1 <- freshIdN t
    b2 <- freshIdN t

    b <- tyBoolT

    let eq = App
                (App 
                    (Prim pr (TyFun t (TyFun t b))) 
                    (Var b1)
                ) 
                (Var b2)

    let c2 = Case (Var i2) i2' [Alt (DataAlt dc [b2]) eq]

    return $ Case (Var i1) i1' [Alt (DataAlt dc [b1]) c2]

lhPPFunc :: Name -> AlgDataTy -> LHStateM Expr
lhPPFunc n adt = do
    let bi = bound_ids adt

    lh <- lhTCM
    lhbi <- mapM (freshIdN . TyApp (TyCon lh TYPE) . TyVar) bi

    b <- tyBoolT
    fs <- mapM (\v -> freshIdN (TyFun (TyVar v) b)) bi

    d <- freshIdN (TyCon n TYPE)

    let lhm = M.fromList $ zip (map idName bi) lhbi
    let fnm = M.fromList $ zip (map idName bi) fs
    e <- lhPPCase lhm fnm adt d

    let e' = mkLams (map (TypeL,) bi ++ map (TermL,) lhbi ++ map (TermL,) fs ++ [(TermL, d)]) e

    return e'

type PPFuncMap = M.Map Name Id

lhPPCase :: LHDictMap -> PPFuncMap -> AlgDataTy -> Id -> LHStateM Expr
lhPPCase lhm fnm adt i = do
    ci <- freshIdN (typeOf i)

    return . Case (Var i) ci =<< mapM (lhPPAlt lhm fnm) (dataCon adt)

lhPPAlt :: LHDictMap -> PPFuncMap -> DataCon -> LHStateM Alt
lhPPAlt lhm fnm dc = do
    ba <- freshIdsN $ anonArgumentTypes dc

    an <- lhAndE
    true <- mkTrueE

    pr <- mapM (\i -> do
                pp <- lhPPCall lhm fnm (typeOf i)
                return $ App pp (Var i)) ba
    let pr' = foldr (\e -> App (App an e)) true pr

    return $ Alt (DataAlt dc ba) pr'

-- This returns an Expr with a function type, of the given Type to Bool.
lhPPCall :: LHDictMap -> PPFuncMap -> Type -> LHStateM Expr
lhPPCall lhm fnm t
    | TyCon _ _ <- tyAppCenter t
    , ts <- tyAppArgs t  = do
        lhpp <- lhPPM

        let lhv = Var $ Id lhpp TyUnknown
        dict <- lhTCDict' lhm t
        undefs <- mapM (lhPPCall lhm fnm) ts

        return . mkApp $ lhv:[Type t, dict] ++ undefs -- ++ [Var i]

    | TyVar (Id n _) <- t
    , Just f <- M.lookup n fnm = return $ Var f -- App (Var f) (Var i)
    | TyVar _ <- tyAppCenter t = do
        i <- freshIdN t
        return . Lam TermL i =<< mkTrueE
    | TyFun _ _ <- t = do
        i <- freshIdN t
        return . Lam TermL i =<< mkTrueE
    | TyForAll _ _ <- t = do
        i <- freshIdN t
        return . Lam TermL i =<< mkTrueE
    |  t == TyLitInt
    || t == TyLitDouble
    || t == TyLitFloat
    || t == TyLitChar = do
        i <- freshIdN t
        return . Lam TermL i =<< mkTrueE
    | otherwise = error $ "\nError in lhPPCall " ++ show t ++ "\n" ++ show lhm

createExtractors :: LHStateM ()
createExtractors = do
    lh <- lhTCM
    eq <- lhEqM

    lt <- lhLtM
    le <- lhLeM
    gt <- lhGtM
    ge <- lhGeM

    ne <- lhNeM
    pp <- lhPPM

    createExtractors' lh [eq, ne, lt, le, gt, ge, pp]

createExtractors' :: Name -> [Name] -> LHStateM ()
createExtractors' lh ns = mapM_ (uncurry (createExtractors'' lh (length ns))) $ zip [0..] ns

createExtractors'' :: Name -> Int -> Int -> Name -> LHStateM ()
createExtractors'' lh i j n = do
    a <- freshIdN TYPE

    bi <- freshIdsN $ replicate i TyUnknown

    li <- freshIdN (TyCon lh (TyApp TYPE TYPE)) 
    ci <- freshIdN (TyCon lh (TyApp TYPE TYPE))

    b <- freshIdN TYPE
    let d = DataCon lh (TyForAll 
                            (NamedTyBndr b) 
                            (TyFun
                                (TyVar b) 
                                (TyApp (TyCon lh (TyApp TYPE TYPE)) (TyVar b))
                            )
                        )
    let c = Case (Var li) ci [Alt (DataAlt d bi) (Var $ bi !! j)]
    let e = Lam TypeL a $ Lam TermL li c

    insertMeasureM n e 
