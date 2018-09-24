{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
module G2.Internals.Liquid.TCGen (createLHTC) where

import G2.Internals.Language
import qualified G2.Internals.Language.KnownValues as KV
import G2.Internals.Language.Monad
import G2.Internals.Liquid.Conversion2
import G2.Internals.Liquid.TCValues
import G2.Internals.Liquid.Types

import Data.Coerce
import Data.Foldable
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import Debug.Trace

createLHTC :: Measures -> KnownValues -> State [FuncCall] -> LHState
createLHTC meenv mkv s =
    let
        (tcv, s') = runStateM (createTCValues mkv) s

        lh_s = consLHState s' meenv tcv
    in
    execLHStateM (do
                    createLHTCFuncs
                    createExtractors) lh_s
    

createTCValues :: KnownValues -> StateM [FuncCall] TCValues
createTCValues kv = do
    lhTCN <- freshSeededStringN "lh"
    lhEqN <- freshSeededStringN "lhEq"
    lhNeN <- freshSeededStringN "lhNe"
    lhPPN <- freshSeededStringN "lhPP"

    return (TCValues { lhTC = lhTCN
                     , lhOrdTC = KV.ordTC kv 

                     , lhEq = lhEqN
                     , lhNe = lhNeN
                     , lhLt = KV.ltFunc kv
                     , lhLe = KV.leFunc kv
                     , lhGt = KV.gtFunc kv
                     , lhGe = KV.geFunc kv

                     , lhPlus = KV.plusFunc kv
                     , lhMinus = KV.minusFunc kv
                     , lhTimes = KV.timesFunc kv
                     , lhDiv = KV.divFunc kv
                     , lhNegate = KV.negateFunc kv
                     , lhMod = KV.modFunc kv

                     , lhPP = lhPPN })

type PredFunc = LHDictMap -> AlgDataTy -> DataCon -> [Id] -> LHStateM [Alt]

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
                                        return (TyConApp n bnvK, f)
                                    Nothing -> error $ "No LH Dict name for " ++ show n) lhm

    tc <- typeClasses
    tcn <- lhTCM
    tci <- freshIdN TYPE
    let tc' = coerce . M.insert tcn (Class { insts = lhtc, typ_ids = [tci] }) $ coerce tc
    putTypeClasses tc'

    -- Now, we do the work of actually generating all the code/functions for the typeclass
    mapM_ (uncurry (createLHTCFuncs' lhm')) . M.toList =<< typeEnv

initalizeLHTC :: Name -> AlgDataTy -> LHStateM (Name, Id)
initalizeLHTC n adt = do
    lhf <- lhName "lh" n
    return (n, Id lhf TyUnknown)

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

    ppN <- lhName "lhPP" n
    pp <- lhPPFunc n adt
    insertMeasureM ppN pp

    -- We define a function to get the LH Dict for this type
    -- It takes and passes on the type arguments, and the LH Dicts for those
    -- type arguments
    lh <- lhTCM

    let bi = bound_ids adt
    let bt = map (Type . TyVar) bi
    lhd <- freshIdsN (map (TyApp (TyConApp lh (TyApp TYPE TYPE)) . TyVar) bi)
    let lhdv = map Var lhd

    let fs = map (\n -> Var (Id n TyUnknown)) [eqN, neN, ppN]
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
            return () -- return (TyConApp n bnvK, fn')
        Nothing -> error $ "No LH Dict name for " ++ show n

lhDCType :: LHStateM Type
lhDCType = do
    lh <- lhTCM
    n <-freshIdN TYPE

    return $ (TyFun
                TyUnknown
                (TyFun
                    TyUnknown
                    (TyFun
                        TyUnknown
                        (TyApp 
                            (TyConApp lh TYPE) 
                            (TyVar n)
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
    lhbi <- mapM (freshIdN . TyApp (TyConApp lh TYPE) . TyVar) bi

    d1 <- freshIdN (TyConApp n TYPE)
    d2 <- freshIdN (TyConApp n TYPE)

    let m = M.fromList $ zip (map idName bi) lhbi
    e <- mkFirstCase cf m n d1 d2 adt

    let e' = mkLams (map (TypeL,) bi ++ map (TermL,) lhbi ++ [(TermL, d1), (TermL, d2)]) e

    return e'

mkFirstCase :: PredFunc -> LHDictMap -> Name -> Id -> Id -> AlgDataTy -> LHStateM Expr
mkFirstCase f ldm n d1 d2 adt@(DataTyCon { data_cons = dcs, bound_ids = bi}) = do
    caseB <- freshIdN (typeOf d1)
    return . Case (Var d1) caseB =<< mapM (mkFirstCase' f ldm d2 adt) dcs
mkFirstCase _ _ _ _ _ _ = return $ Var (Id (Name "Bad mkFirstCase" Nothing 0 Nothing) TyUnknown)

mkFirstCase' :: PredFunc -> LHDictMap -> Id -> AlgDataTy -> DataCon -> LHStateM Alt
mkFirstCase' f ldm d2 adt dc = do
    ba <- freshIdsN $ anonArgumentTypes dc

    return . Alt (DataAlt dc ba) =<< mkSecondCase f ldm d2 adt dc ba

mkSecondCase :: PredFunc -> LHDictMap -> Id -> AlgDataTy -> DataCon -> [Id] -> LHStateM Expr
mkSecondCase f ldm d2 adt dc ba1 = do
    caseB <- freshIdN (typeOf dc)

    alts <- f ldm adt dc ba1

    return $ Case (Var d2) caseB alts

lhEqFunc :: PredFunc
lhEqFunc ldm adt dc ba1 = do
    ba2 <- freshIdsN $ anonArgumentTypes dc

    an <- mkAndE
    true <- mkTrueE
    false <- mkFalseE

    pr <- mapM (uncurry (eqLHFuncCall ldm)) $ zip ba1 ba2
    let pr' = foldr (\e -> App (App an e)) true pr

    return [ Alt Default false
           , Alt (DataAlt dc ba2) pr'] 

eqLHFuncCall :: LHDictMap -> Id -> Id -> LHStateM Expr
eqLHFuncCall ldm i1 i2
    | TyConApp n _ <- tyAppCenter t
    , ts <- tyAppArgs t  = do
        lhe <- lhEqM

        i <- freshIdN TYPE
        b <- tyBoolT

        let lhv = Var $ Id lhe (TyForAll (NamedTyBndr i) (TyFun (TyVar i) (TyFun (TyVar i) b)))
        let as = map Type ts
        
        return $ foldl' App lhv [Var i1, Var i2]

    | TyVar _ <- t = do
        lhe <- lhEqM

        i <- freshIdN TYPE
        b <- tyBoolT

        let lhv = App (Var (Id lhe (TyForAll (NamedTyBndr i) (TyFun (TyVar i) (TyFun (TyVar i) b))))) (Type t)
        return $ App (App lhv (Var i1)) (Var i2)

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
lhNeFunc ldm adt dc ba1 = do
    ba2 <- freshIdsN $ anonArgumentTypes dc

    an <- mkAndE
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

lhPPFunc :: Name -> AlgDataTy -> LHStateM Expr
lhPPFunc n adt = do
    let bi = bound_ids adt

    lh <- lhTCM
    lhbi <- mapM (freshIdN . TyApp (TyConApp lh TYPE) . TyVar) bi

    b <- tyBoolT
    fs <- mapM (\v -> freshIdN (TyFun (TyVar v) b)) bi

    d <- freshIdN (TyConApp n TYPE)

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

    an <- mkAndE
    true <- mkTrueE

    pr <- mapM (lhPPCall lhm fnm) ba
    let pr' = foldr (\e -> App (App an e)) true pr

    return $ Alt (DataAlt dc ba) pr'

lhPPCall :: LHDictMap -> PPFuncMap -> Id -> LHStateM Expr
lhPPCall lhm fnm i@(Id _ t)
    | TyConApp n _ <- tyAppCenter t
    , ts <- tyAppArgs t  = do
        lhpp <- lhPPM

        let lhv = Var $ Id lhpp TyUnknown
        dict <- lhTCDict'' lhm t
        let undefs = map (const $ Prim Undefined TyBottom) $ typeArgs dict

        return . mkApp $ lhv:[Type t, dict] ++ undefs ++ [Var i]

    | TyVar _ <- tyAppCenter t
    , ts <- tyAppArgs t = do
        lhpp <- lhPPM
        dict <- lhTCDict'' lhm t
        let undefs = map (const $ Prim Undefined TyBottom) $ typeArgs dict
        return . mkApp $ [Var (Id lhpp TyUnknown), Type t, dict] ++ undefs ++ [Var i]

    | TyFun _ _ <- t = mkTrueE
    | TyForAll _ _ <- t = mkTrueE
    |  t == TyLitInt
    || t == TyLitDouble
    || t == TyLitFloat
    || t == TyLitChar = mkTrueE
    | otherwise = error $ "\nError in lhPPCall " ++ show t ++ "\n" ++ show lhm

typeArgs :: Expr -> [Type]
typeArgs = mapMaybe typeOfTypeExpr . unApp

typeOfTypeExpr :: Expr -> Maybe Type
typeOfTypeExpr (Type t) = Just t
typeOfTypeExpr _ = Nothing

createExtractors :: LHStateM ()
createExtractors = do
    lh <- lhTCM
    eq <- lhEqM
    ne <- lhNeM
    pp <- lhPPM

    createExtractors' lh [eq, ne, pp]

createExtractors' :: Name -> [Name] -> LHStateM ()
createExtractors' lh ns = mapM_ (uncurry (createExtractors'' lh (length ns))) $ zip [0..] ns

createExtractors'' :: Name -> Int -> Int -> Name -> LHStateM ()
createExtractors'' lh i j n = do
    a <- freshIdN TYPE
    let tva = TyVar a

    bi <- freshIdsN $ replicate i TyUnknown

    li <- freshIdN (TyConApp lh (TyApp TYPE TYPE)) 
    ci <- freshIdN (TyConApp lh (TyApp TYPE TYPE))

    b <- freshIdN TYPE
    let d = DataCon lh (TyForAll 
                            (NamedTyBndr b) 
                            (TyFun
                                (TyVar b) 
                                (TyApp (TyConApp lh (TyApp TYPE TYPE)) (TyVar b))
                            )
                        )
    let c = Case (Var li) ci [Alt (DataAlt d bi) (Var $ bi !! j)]
    let e = Lam TypeL a $ Lam TermL li c

    insertMeasureM n e 
