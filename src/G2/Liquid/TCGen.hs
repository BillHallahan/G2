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
import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T
import G2.Language (leadingTyForAllBindings)
import qualified G2.Language.TyVarEnv as TV 

-- | Creates an LHState.  This involves building a TCValue, and
-- creating the new LH TC which checks equality, and has a function to
-- check refinements of polymorphic types
createLHState :: TV.TyVarEnv -> Measures -> KnownValues -> TypeClasses -> State [FuncCall] -> Bindings -> (LHState, Bindings)
createLHState tv meenv mkv mtc s b =
    let
        (tcv, (s', b')) = runStateM (createTCValues mkv (type_env s)) s b

        lh_s = consLHState s' meenv mkv mtc tcv
    in
    execLHStateM (do
                    createLHTCFuncs tv
                    createExtractors tv) lh_s b'
    

createTCValues :: KnownValues -> TypeEnv -> StateM [FuncCall] TCValues
createTCValues kv tenv = do
    lhTCN <- freshSeededStringN "lh"
    lhEqN <- freshSeededStringN "lhEq"
    lhNeN <- freshSeededStringN "lhNe"

    lhLtN <- freshSeededStringN "lhLt"
    lhLeN <- freshSeededStringN "lhLe"
    lhGtN <- freshSeededStringN "lhGt"
    lhGeN <- freshSeededStringN "lhGe"

    lhPPN <- freshSeededStringN "lhPP"
    lhNuOr <- freshSeededStringN "lhNuOr"
    lhOrdN <- freshSeededStringN "lhOrd"

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
                        , lhToInteger = KV.toIntegerFunc kv

                        , lhFromRational = KV.fromRationalFunc kv

                        , lhToRatioFunc = KV.toRatioFunc kv

                        , lhNumOrd = lhNuOr

                        , lhAnd = KV.andFunc kv
                        , lhOr = KV.orFunc kv
                        , lhNot = KV.notFunc kv

                        , lhImplies = KV.impliesFunc kv
                        , lhIff = KV.iffFunc kv

                        , lhPP = lhPPN

                        , lhOrd = lhOrdN

                        , lhSet = nameModMatch (Name "Set" (Just "Data.Set.Internal") 0 Nothing) tenv})

    return tcv

type PredFunc = LHDictMap -> Name -> AlgDataTy -> DataCon -> [Id] -> LHStateM [Alt]

createLHTCFuncs :: TV.TyVarEnv -> LHStateM ()
createLHTCFuncs tv = do
    lhm <- mapM (uncurry initalizeLHTC) . HM.toList =<< typeEnv
    let lhm' = HM.fromList lhm

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
    let tc' = insertClass tcn (Class { insts = lhtc, typ_ids = [tci], superclasses = [] }) tc
    putTypeClasses tc'

    -- Now, we do the work of actually generating all the code/functions for the typeclass
    mapM_ (uncurry (createLHTCFuncs' tv lhm')) . HM.toList =<< typeEnv

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
                (TyCon lh (TyFun TYPE TYPE)) 
                ct
            )

    let t' = foldr TyFun t $ map (TyApp (TyCon lh (TyFun TYPE TYPE)) . TyVar) bi
    let t'' = foldr TyForAll t' bi
    return t''

lhName :: T.Text -> Name -> LHStateM Name
lhName t (Name n m _ _) = freshSeededNameN $ Name (t `T.append` n) m 0 Nothing

createLHTCFuncs' :: TV.TyVarEnv -> LHDictMap -> Name -> AlgDataTy -> LHStateM ()
createLHTCFuncs' tv lhm n adt = do
    eqN <- lhName "lhEq" n
    eq <- createFunc tv (lhEqFunc tv) n adt
    insertMeasureM eqN eq

    neN <- lhName "lhNe" n
    ne <- createFunc tv (lhNeFunc tv) n adt
    insertMeasureM neN ne

    ltN <- lhName "lhLt" n
    lt <- createLtFunc tv n adt
    insertMeasureM ltN lt

    leN <- lhName "lhLe" n
    le <- createLeFunc tv n adt
    insertMeasureM leN le

    gtN <- lhName "lhGt" n
    gt <- createGtFunc tv n adt
    insertMeasureM gtN gt

    geN <- lhName "lhGe" n
    ge <- createGeFunc tv n adt
    insertMeasureM geN ge

    ppN <- lhName "lhPP" n
    pp <- lhPPFunc tv n adt
    insertMeasureM ppN pp

    -- We also put the Ord typeclass into the LH TC, if it exists.
    ord <- ordTCM
    ordDict <- lookupTCDictTC ord (TyCon n TyUnknown)
    ordE <- case ordDict of
                    Just i -> return (Var i)
                    _ -> do
                        flse <- mkFalseE
                        return (Assume Nothing flse (Prim Undefined TyUnknown))

    -- We define a function to get the LH Dict for this type
    -- It takes and passes on the type arguments, and the LH Dicts for those
    -- type arguments
    lh <- lhTCM

    let bi = bound_ids adt
    let bt = map (Type . TyVar) bi
    lhd <- freshIdsN (map (TyApp (TyCon lh (TyApp TYPE TYPE)) . TyVar) bi)
    let lhdv = map Var lhd


    let fs = map (\(n', t) -> Var (Id n' t)) [ (eqN, (typeOf tv eq))
                                             , (neN, (typeOf tv ne))
                                             , (ltN, (typeOf tv lt))
                                             , (leN, (typeOf tv le))
                                             , (gtN, (typeOf tv gt))
                                             , (geN, (typeOf tv ge))
                                             , (ppN, (typeOf tv pp))]
    let fs' = map (\f -> mkApp $ f:bt ++ lhdv) fs ++ [ordE]

    lhdct <- lhDCType
    let ue = leadingTyForAllBindings (typeOf tv lhdct)
    let e = mkApp $ Data (DataCon lh lhdct ue []):Type (TyCon n TyUnknown):fs'
    let e' = foldr (Lam TermL) e lhd
    let e'' = foldr (Lam TypeL) e' bi

    let fn = HM.lookup n lhm

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
    let i = Id a TYPE
    let tva = TyVar i
    let taab = TyFun tva (TyFun tva bool)


    return $ TyForAll i
            (TyFun
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
                                        (TyFun
                                            TyUnknown
                                            (TyApp 
                                                (TyCon lh (TyFun TYPE TYPE)) 
                                                (TyVar n)
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )

createFunc :: TV.TyVarEnv -> PredFunc -> Name -> AlgDataTy -> LHStateM Expr 
createFunc tv cf n adt = do
    -- Our function needs the following arguments:
    -- Type arguments
    -- A LH typeclass for each type argument
    -- Two expression of the adt type
    -- We set up the needed Ids here
    let bi = bound_ids adt

    lh <- lhTCM
    lhbi <- mapM (freshIdN . TyApp (TyCon lh (TyFun TYPE TYPE)) . TyVar) bi

    d1 <- freshIdN (TyCon n TYPE)
    d2 <- freshIdN (TyCon n TYPE)

    let m = HM.fromList $ zip (map idName bi) lhbi
    e <- mkFirstCase tv cf m d1 d2 n adt

    let e' = mkLams (map (TypeL,) bi ++ map (TermL,) lhbi ++ [(TermL, d1), (TermL, d2)]) e

    return e'

mkFirstCase :: TV.TyVarEnv -> PredFunc -> LHDictMap -> Id -> Id -> Name -> AlgDataTy -> LHStateM Expr
mkFirstCase tv f ldm d1 d2 n adt@(DataTyCon { data_cons = dcs }) = do
    caseB <- freshIdN (typeOf tv d1)
    boolT <- tyBoolT
    return . Case (Var d1) caseB boolT =<< mapM (mkFirstCase' tv f ldm d2 n adt) dcs
mkFirstCase tv f ldm d1 d2 n adt@(NewTyCon { data_con = dc }) = do
    caseB <- freshIdN (typeOf tv d1)
    boolT <- tyBoolT
    return . Case (Var d1) caseB boolT . (:[]) =<< mkFirstCase' tv f ldm d2 n adt dc
mkFirstCase _ _ _ _ _ _ _ = error "mkFirstCase: Unsupported AlgDataTy"

mkFirstCase' :: TV.TyVarEnv -> PredFunc -> LHDictMap -> Id -> Name -> AlgDataTy -> DataCon -> LHStateM Alt
mkFirstCase' tv f ldm d2 n adt dc = do
    ba <- freshIdsN $ anonArgumentTypes $ typeOf tv dc

    return . Alt (DataAlt dc ba) =<< mkSecondCase tv f ldm d2 n adt dc ba

mkSecondCase :: TV.TyVarEnv -> PredFunc -> LHDictMap -> Id -> Name -> AlgDataTy -> DataCon -> [Id] -> LHStateM Expr
mkSecondCase tv f ldm d2 n adt dc ba1 = do
    caseB <- freshIdN (typeOf tv dc)

    alts <- f ldm n adt dc ba1

    boolT <- tyBoolT

    return $ Case (Var d2) caseB boolT alts

lhEqFunc :: TV.TyVarEnv -> PredFunc
lhEqFunc tv ldm _ _ dc ba1 = do
    ba2 <- freshIdsN $ anonArgumentTypes $ typeOf tv dc

    an <- lhAndE
    true <- mkTrueE
    false <- mkFalseE

    pr <- mapM (uncurry (eqLHFuncCall tv ldm)) $ zip ba1 ba2
    let pr' = foldr (\e -> App (App an e)) true pr

    return [ Alt Default false
           , Alt (DataAlt dc ba2) pr'] 

eqLHFuncCall :: TV.TyVarEnv -> LHDictMap -> Id -> Id -> LHStateM Expr
eqLHFuncCall tv ldm i1 i2
    | TyCon _ _ <- tyAppCenter t = do
        lhe <- lhEqM

        i <- freshIdN TYPE
        b <- tyBoolT

        lhd <- lhTCDict' ldm t
        let lhv = App (Var $ Id lhe (TyForAll i (TyFun (typeOf tv lhd) (TyFun (TyVar i) (TyFun (TyVar i) b))))) (Type t)

        return $ foldl' App (App lhv lhd) [Var i1, Var i2]

    | TyVar _ <- t = do
        lhe <- lhEqM

        i <- freshIdN TYPE
        b <- tyBoolT

        lhd <- lhTCDict' ldm t

        let lhv = App (Var (Id lhe (TyForAll i (TyFun (typeOf tv lhd) (TyFun (TyVar i) (TyFun (TyVar i) b)))))) (Type t)
        return $ App (App (App lhv lhd) (Var i1)) (Var i2)

    | TyFun _ _ <- t = mkTrueE
    | TyApp _ _ <- t = mkTrueE
    | TyForAll _ _ <- t = mkTrueE
    
    |  t == TyLitDouble
    || t == TyLitFloat = do
        b <- tyBoolT
        let pt = TyFun t (TyFun t b)
        
        return $ App (App (Prim FpEq pt) (Var i1)) (Var i2)

    |  t == TyLitInt
    || t == TyLitWord
    || t == TyLitRational
    || t == TyLitChar = do
        b <- tyBoolT
        let pt = TyFun t (TyFun t b)
        
        return $ App (App (Prim Eq pt) (Var i1)) (Var i2)

    | otherwise = error $ "\nError in eqLHFuncCall " ++ show t ++ "\n" ++ show ldm
    where
        t = typeOf tv i1

lhNeFunc :: TV.TyVarEnv -> PredFunc
lhNeFunc tv ldm _ _ dc ba1 = do
    ba2 <- freshIdsN $ anonArgumentTypes $ typeOf tv dc

    an <- lhAndE
    true <- mkTrueE
    false <- mkFalseE

    trueDC <- mkDCTrueM
    falseDC <- mkDCFalseM

    tBool <- tyBoolT

    pr <- mapM (uncurry (eqLHFuncCall tv ldm)) $ zip ba1 ba2
    let pr' = foldr (\e -> App (App an e)) true pr

    b <- freshIdN =<< tyBoolT
    let pr'' = Case pr' b tBool [ Alt (DataAlt trueDC []) false
                                , Alt (DataAlt falseDC []) true ]

    return [ Alt Default false
           , Alt (DataAlt dc ba2) pr''] 

createLtFunc :: TV.TyVarEnv -> Name -> AlgDataTy -> LHStateM Expr
createLtFunc tv = createOrdFunc tv Lt FpLt

createLeFunc :: TV.TyVarEnv -> Name -> AlgDataTy -> LHStateM Expr
createLeFunc tv = createOrdFunc tv Le FpLeq

createGtFunc :: TV.TyVarEnv -> Name -> AlgDataTy -> LHStateM Expr
createGtFunc tv = createOrdFunc tv Gt FpGt

createGeFunc :: TV.TyVarEnv -> Name -> AlgDataTy -> LHStateM Expr
createGeFunc tv = createOrdFunc tv Ge FpGeq

type IntPrimitive = Primitive
type FpPrimitive = Primitive

-- We currently treat relations between Ints/Floats/Doubles correctly,
-- and just assume all other relations are true.
-- In LH, relations between x :: T and y :: T work by checking that
--    f x < f y
-- for all f :: T -> Int, so this could make us miss some counterexamples.
-- However, we will never generate an incorrect counterexample.
-- (i.e. it is sound but incomplete)
createOrdFunc :: TV.TyVarEnv -> IntPrimitive -> FpPrimitive -> Name -> AlgDataTy -> LHStateM Expr 
createOrdFunc tv int_prim fp_prim n adt = do
    let bi = bound_ids adt

    lh <- lhTCM
    lhbi <- mapM (freshIdN . TyApp (TyCon lh (TyFun TYPE TYPE)) . TyVar) bi

    d1 <- freshIdN (TyCon n TYPE)
    d2 <- freshIdN (TyCon n TYPE)

    kv <- knownValues
    e <- mkOrdCases tv int_prim fp_prim kv d1 d2 n adt

    let e' = mkLams (map (TypeL,) bi ++ map (TermL,) lhbi ++ [(TermL, d1), (TermL, d2)]) e

    return e'

mkOrdCases :: TV.TyVarEnv -> IntPrimitive -> FpPrimitive -> KnownValues -> Id -> Id -> Name -> AlgDataTy -> LHStateM Expr
mkOrdCases tv int_prim fp_prim kv i1 i2 n (DataTyCon { data_cons = [dc]})
    | n == KV.tyInt kv = mkPrimOrdCases tv int_prim TyLitInt i1 i2 dc
    | n == KV.tyInteger kv = mkPrimOrdCases tv int_prim TyLitInt i1 i2 dc
    | n == KV.tyFloat kv = mkPrimOrdCases tv fp_prim TyLitFloat i1 i2 dc
    | n == KV.tyDouble kv = mkPrimOrdCases tv fp_prim TyLitDouble i1 i2 dc
    | otherwise = mkTrueE
mkOrdCases _ _ _ _ _ _ _ _ = mkTrueE

mkPrimOrdCases :: TV.TyVarEnv -> Primitive -> Type -> Id -> Id -> DataCon -> LHStateM Expr
mkPrimOrdCases tv pr t i1 i2 dc = do
    i1' <- freshIdN (typeOf tv dc)
    i2' <- freshIdN (typeOf tv dc)

    b1 <- freshIdN t
    b2 <- freshIdN t

    b <- tyBoolT

    let eq = App
                (App 
                    (Prim pr (TyFun t (TyFun t b))) 
                    (Var b1)
                ) 
                (Var b2)

    let c2 = Case (Var i2) i2' b [Alt (DataAlt dc [b2]) eq]

    return $ Case (Var i1) i1' b [Alt (DataAlt dc [b1]) c2]

lhPPFunc :: TV.TyVarEnv -> Name -> AlgDataTy -> LHStateM Expr
lhPPFunc tv n adt = do
    let bi = bound_ids adt

    lh <- lhTCM
    lhbi <- mapM (freshIdN . TyApp (TyCon lh (TyFun TYPE TYPE)) . TyVar) bi

    b <- tyBoolT
    fs <- mapM (\v -> freshIdN (TyFun (TyVar v) b)) bi

    let k = foldr (const (TyApp TYPE)) TYPE bi
        t = foldl' TyApp (TyCon n k) (map TyVar bi)
    d <- freshIdN t -- (TyCon n TYPE)

    let lhm = HM.fromList $ zip (map idName bi) lhbi
    let fnm = HM.fromList $ zip (map idName bi) fs
    e <- lhPPCase tv lhm fnm adt d

    let e' = mkLams (map (TypeL,) bi ++ map (TermL,) lhbi ++ map (TermL,) fs ++ [(TermL, d)]) e

    return e'

type PPFuncMap = HM.HashMap Name Id

lhPPCase :: TV.TyVarEnv -> LHDictMap -> PPFuncMap -> AlgDataTy -> Id -> LHStateM Expr
lhPPCase tv lhm fnm (DataTyCon { data_cons = dcs }) i = do
    ci <- freshIdN (typeOf tv i)
    tBool <- tyBoolT

    return . Case (Var i) ci tBool =<< mapM (lhPPAlt tv lhm fnm) dcs
lhPPCase tv lhm fnm (NewTyCon { rep_type = rt }) i = do
    pp <- lhPPCall tv lhm fnm rt
    let c = Cast (Var i) (typeOf tv i :~ rt)
    return $ App pp c


lhPPAlt :: TV.TyVarEnv -> LHDictMap -> PPFuncMap -> DataCon -> LHStateM Alt
lhPPAlt tv lhm fnm dc = do
    ba <- freshIdsN $ anonArgumentTypes $ typeOf tv dc

    an <- lhAndE
    true <- mkTrueE

    pr <- mapM (\i -> do
                pp <- lhPPCall tv lhm fnm (typeOf tv i)
                return $ App pp (Var i)) ba
    let pr' = foldr (\e -> App (App an e)) true pr

    return $ Alt (DataAlt dc ba) pr'

-- This returns an Expr with a function type, of the given Type to Bool.
lhPPCall :: TV.TyVarEnv -> LHDictMap -> PPFuncMap -> Type -> LHStateM Expr
lhPPCall tv lhm fnm t
    | TyCon _ _ <- tyAppCenter t
    , ts <- tyAppArgs t  = do
        lhpp <- lhPPM

        let lhv = Var $ Id lhpp TyUnknown
        dict <- lhTCDict' lhm t
        undefs <- mapM (lhPPCall tv lhm fnm) ts

        return . mkApp $ lhv:[Type t, dict] ++ undefs -- ++ [Var i]

    | TyVar (Id n _) <- t
    , Just f <- HM.lookup n fnm = return $ Var f -- App (Var f) (Var i)
    | TyVar _ <- tyAppCenter t = do
        i <- freshIdN t
        return . Lam TermL i =<< mkTrueE
    | TyFun _ _ <- t = do
        let ts = anonArgumentTypes t
            rt = returnType t
        let_is <- freshIdsN ts
        bind_i <- freshIdN t
        let bind_app = mkApp $ Var bind_i:map Var let_is
        pp <- lhPPCall tv lhm fnm rt
        let pp_app = App pp bind_app
        return . Lam TermL bind_i $ Let (zip let_is $ map (SymGen SNoLog) ts) pp_app
        -- i <- freshIdN t
        -- return . Lam TermL i =<< mkTrueE
    | TyForAll _ _ <- t = do
        i <- freshIdN t
        return . Lam TermL i =<< mkTrueE
    | isPrimType t = do
        i <- freshIdN t
        return . Lam TermL i =<< mkTrueE
    | otherwise = error $ "\nError in lhPPCall " ++ show t ++ "\n" ++ show lhm

createExtractors :: TV.TyVarEnv -> LHStateM ()
createExtractors tv = do
    lh <- lhTCM
    eq <- lhEqM

    lt <- lhLtM
    le <- lhLeM
    gt <- lhGtM
    ge <- lhGeM

    ne <- lhNeM
    pp <- lhPPM

    ord <- lhOrdM

    createExtractors' tv lh [eq, ne, lt, le, gt, ge, pp, ord]

createExtractors' :: TV.TyVarEnv -> Name -> [Name] -> LHStateM ()
createExtractors' tv lh ns = mapM_ (uncurry (createExtractors'' tv lh (length ns))) $ zip [0..] ns

createExtractors'' :: TV.TyVarEnv -> Name -> Int -> Int -> Name -> LHStateM ()
createExtractors'' tv lh i j n = do
    a <- freshIdN TYPE

    bi <- freshIdsN $ replicate i TyUnknown

    li <- freshIdN (TyCon lh (TyFun TYPE TYPE)) 
    ci <- freshIdN (TyCon lh (TyFun TYPE TYPE))

    b <- freshIdN TYPE
    let d = DataCon lh (TyForAll 
                            b
                            (TyFun
                                (TyVar b) 
                                (TyApp (TyCon lh (TyFun TYPE TYPE)) (TyVar b))
                            )
                        )
                        [b]
                        []
    let vi = bi !! j
        c = Case (Var li) ci (typeOf tv vi) [Alt (DataAlt d bi) (Var vi)]
    let e = Lam TypeL a $ Lam TermL li c

    insertMeasureM n e 
