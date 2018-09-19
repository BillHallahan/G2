{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
module G2.Internals.Liquid.TCGen (createLHTC) where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.KnownValues as KV
import G2.Internals.Language.Monad
import G2.Internals.Liquid.Conversion2
import G2.Internals.Liquid.TCValues
import G2.Internals.Liquid.Types

import Control.Monad
import Control.Monad.Extra (maybeM)

import Data.Coerce
import Data.Foldable
import Data.List
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
-- genTC :: Name -> [(Name, Type, Walkers)] -> LHStateM ()
-- genTC tcn ntws = do
--     tc <- typeClasses    

--     let (fn, ts, ws) = unzip3 ntws

--     dcN <- freshSeededNameN tcn

--     let dc = DataCon dcN (mkTyFun (ts ++ [TyConApp dcN TYPE]))

--         adt = DataTyCon { bound_ids = []
--                         , data_cons = [dc] }

--     insertT tcn adt

--     tenv <- typeEnv

--     -- Get type names
--     let ns = M.keys tenv

--     ti <- genTCFuncs tcn [] dc ns ws

--     tci <- freshIdN TYPE

--     let tc' = coerce . M.insert tcn (Class { insts = ti, typ_ids = [tci] }) $ coerce tc

--     --Create functions to access the TC functions
--     access <- sequence $ map (accessFunction tcn dc) [0..length fn]

--     sequence_ $ map (uncurry insertMeasureM) (zip fn access)
    
--     putTypeClasses tc'

-- genTCFuncs :: Name -> [(Type, Id)] -> DataCon -> [Name] -> [Walkers] -> LHStateM [(Type, Id)]
-- genTCFuncs _ ti _ [] _ = return ti
-- genTCFuncs lh ti dc (n:ns) ws = do
--     fn <- lhFuncName n

--     t <- lookupT n

--     let
--         bn = case fmap bound_ids t of
--             Just bn' -> bn'
--             Nothing -> error "Bound names not found in genTCFuncs"

--         bnv = map TyVar bn
--         bnvK = mkTyApp $ map (const TYPE) bnv
--         tbnv = map Type bnv

--         fs = mapMaybe (M.lookup n) ws
--         vs = map Var fs
--         vs' = map (\v -> mkApp $ v:tbnv) vs

--         e = mkLams (map (TypeL,) bn) $ mkApp $ Data dc:vs'

--     insertMeasureM fn e

--     let
--         t' = TyApp (TyConApp lh (TyFun TYPE TYPE)) (TyConApp n bnvK)

--         ti' = (TyConApp n bnvK, Id fn t'):ti
    
--     genTCFuncs lh ti' dc ns ws

-- lhFuncName :: Name -> LHStateM Name
-- lhFuncName n = freshSeededStringN ("lh" `T.append` nameOcc n `T.append` "Func")

-- | accessFunction
--Create a function to access a TC function from the ADT
-- accessFunction :: Name -> DataCon -> Int -> LHStateM Expr
-- accessFunction tcn dc@(DataCon _ t) i = do
--     let t' = TyConApp tcn TYPE

--         -- This gets bound to the Type (Expr constructor) argument
--     tb <- freshIdN TYPE

--     lb <- freshIdN t'
--     cb <- freshIdN t'

--     is <- freshIdsN $ anonArgumentTypes $ PresType t

--     let
--         a = Alt (DataAlt dc is) $ Var (is !! i)

--         c = Case (Var lb) cb [a]
    
--     return (Lam TypeL tb (Lam TermL lb c))
    -- return (Lam TermL lb (Lam TypeL tb c))

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
    lhLtN <- freshSeededStringN "lhLt"
    lhLeN <- freshSeededStringN "lhLe"
    lhGtN <- freshSeededStringN "lhGt"
    lhGeN <- freshSeededStringN "lhGe"
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

-- TODO: very similar to createFuncsM in Language/CreateFuncs.hs
-- createFuncsM' :: [b]
--               -> s
--               -> (b -> LHStateM Name)
--               -> (b -> Name -> s -> LHStateM s)
--               -> (s -> b -> LHStateM Expr)
--               -> LHStateM s
-- createFuncsM' genFrom store namef storef exprf = do
--     ns <- freshSeededNamesN =<< mapM namef genFrom

--     let genFromNames = zip genFrom ns
--     -- let fullStore = foldr (uncurry storef) store genFromNames
--     fullStore <- foldM (\s (b, n) -> storef b n s) store genFromNames

--     exprfs <- mapM (exprf fullStore) genFrom

--     sequence_ $ map (uncurry insertMeasureM) (zip ns exprfs)

--     return fullStore

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

    ltN <- lhName "lhLt" n
    -- lt <- createFunc lhLtFunc n adt
    -- insertMeasureM ltN lt

    leN <- lhName "lhLe" n
    -- le <- createFunc lhLeFunc n adt
    -- insertMeasureM leN le

    gtN <- lhName "lhGt" n
    -- gt <- createFunc lhGtFunc n adt
    -- insertMeasureM gtN gt

    geN <- lhName "lhGe" n
    -- ge <- createFunc lhGeFunc n adt
    -- insertMeasureM geN ge

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

    let e = mkApp $ Data (DataCon lh TyUnknown):fs'
    let e' = foldr (Lam TermL) e lhd
    let e'' = foldr (Lam TypeL) e' bi

    let fn = M.lookup n lhm

    case fn of
        Just fn' -> do
            insertMeasureM (idName fn') e''
            -- let bnvK = mkTyApp $ map (const TYPE) bi
            return () -- return (TyConApp n bnvK, fn')
        Nothing -> error $ "No LH Dict name for " ++ show n

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
        let lhv = App (Var (Id lhe TyUnknown)) (Type t)
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
lhNeFunc ldm adt dc ba1 = return []

lhLtFunc :: PredFunc
lhLtFunc ldm adt dc ba1 = return []

lhLeFunc :: PredFunc
lhLeFunc ldm adt dc ba1 = return []

lhGtFunc :: PredFunc
lhGtFunc ldm adt dc ba1 = return []

lhGeFunc :: PredFunc
lhGeFunc ldm adt dc ba1 = return []

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
        let lhv = App (Var (Id lhpp TyUnknown)) (Type t)
        return $ App lhv (Var i)
    
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

-- | t <- typeOf i
--     , TyConApp n _ <- tyAppCenter t
--     , ts <- tyAppArgs t
--     , Just f <- M.lookup n w =
--         let
--             as = map Type ts
--             as' = map (polyPredFunc' true w bnf) ts
--         in
--         foldl' App (Var f) (as ++ as')

createExtractors :: LHStateM ()
createExtractors = do
    lh <- lhTCM
    eq <- lhEqM
    ne <- lhNeM
    -- lt <- lhLtM
    -- le <- lhLeM
    -- gt <- lhGtM
    -- ge <- lhGeM
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


-- eqLHFuncCall :: Name -> Walkers -> [(Name, Id)] -> Expr -> Expr -> LHStateM Expr
-- eqLHFuncCall lhExN w _ e e'
--     | t <- typeOf e
--     , TyConApp n _ <- tyAppCenter t
--     , ts <- tyAppArgs t
--     , Just f <- M.lookup n w =
--         let
--             as = map Type ts
--         in
--         return $ foldl' App (Var f) (as ++ [e, e'])
--     | t@(TyVar _) <- typeOf e =
--         let
--             c = App (Var (Id lhExN TyUnknown)) (Type t)
--         in
--         return $ App (App c e) e'
--     | TyFun _ _ <- typeOf e = mkTrueE
--     | TyForAll _ _ <- typeOf e = mkTrueE
--     | t <- typeOf e
--     ,  t == TyLitInt
--     || t == TyLitDouble
--     || t == TyLitFloat
--     || t == TyLitChar = do
--         b <- tyBoolT
--         let pt = TyFun t (TyFun t b)
        
--         return $ App (App (Prim Eq pt) e) e'
--     | otherwise = error $ "\nError in eqLHFuncCall " ++ show (typeOf e)


-- createLHTCFuncs :: LHStateM ()
-- createLHTCFuncs = do
--     tenv <- typeEnv

--     let tenv' = M.toList tenv

--     lhTCN <- lhTCM
--     lhEqN <- lhEqM
--     lhNeN <- lhNeM
--     lhLtN <- lhLtM
--     lhLeN <- lhLeM
--     lhGtN <- lhGtM
--     lhGeN <- lhGeM
--     lhPPN <- lhPPM

--     eq_w <- createFuncsM' tenv' M.empty (return . lhEqName . fst) lhStore (lhTEnvExpr lhTCN (lhEqCase2Alts lhEqN) (eqLHFuncCall lhEqN))
--     neq_w <- createFuncsM' tenv' M.empty (return . lhNeqName . fst) lhStore (lhNeqExpr lhTCN eq_w)
--     lt_w <- createFuncsM' tenv' M.empty (return . lhLtName . fst) lhStore (lhTEnvExpr lhTCN (lhLtCase2Alts lhLtN) (ltLHFuncCall lhLtN))

--     le_w <- createFuncsM' tenv' M.empty (return . lhLeName . fst) lhStore (lhLeExpr lt_w eq_w)
--     gt_w <- createFuncsM' tenv' M.empty (return . lhGtName . fst) lhStore (lhGtExpr lt_w)
--     ge_w <- createFuncsM' tenv' M.empty (return . lhGeName . fst) lhStore (lhGeExpr le_w)

--     pp_w <- createFuncsM' tenv' M.empty (return . lhPolyPredName . fst) lhStore (lhPolyPred lhTCN)

--     let primN = [Name "Int#" (Just "GHC.Prims") 0 Nothing, Name "Float#" (Just "GHC.Prims") 0 Nothing, Name "Double#" (Just "GHC.Prims") 0 Nothing]
--     eq_w2 <- createPrimFuncs eq_w Eq primN
--     neq_w2 <- createPrimFuncs neq_w Neq primN
--     lt_w2 <- createPrimFuncs lt_w Lt primN
--     le_w2 <- createPrimFuncs le_w Le primN
--     gt_w2 <- createPrimFuncs gt_w Gt primN
--     ge_w2 <- createPrimFuncs ge_w Ge primN

--     pp_w2 <- createPrimPolyPreds pp_w primN

--     tb <- tyBoolT

--     tvAN <- freshSeededStringN "a"

--     let tvA = TyVar $ Id tvAN TYPE

--     genTC lhTCN
--         [ (lhEqN, TyFun tvA (TyFun tvA tb), eq_w2) 
--         , (lhNeN, TyFun tvA (TyFun tvA tb), neq_w2)
--         , (lhLtN, TyFun tvA (TyFun tvA tb), lt_w2)
--         , (lhLeN, TyFun tvA (TyFun tvA tb), le_w2)
--         , (lhGtN, TyFun tvA (TyFun tvA tb), gt_w2)
--         , (lhGeN, TyFun tvA (TyFun tvA tb), ge_w2)
--         , (lhPPN, TyFun (TyFun tvA tb) tb, pp_w2) ]

---------------------------------------
-- Gen Helper
---------------------------------------

-- lhStore :: (Name, AlgDataTy) -> Name -> Walkers -> LHStateM Walkers
-- lhStore (n, adt) n' w = do
--     let 
--         bn = bound_ids adt
--         bnt = map (typeOf) bn
--         bnf = map (\b -> TyFun b b) bnt

--         base = TyFun (TyConApp n TYPE) (TyConApp n TYPE)

--         t = foldr TyFun base (bnt ++ bnf)
--         i = Id n' t
    
--     return (M.insert n i w)

-- -- Returns bindings for TYPE parameters and cooresponding LH typeclasses
-- boundNameBindings :: Name -> AlgDataTy -> LHStateM (AlgDataTy, [(LamUse, Id)], [(LamUse, Id)])
-- boundNameBindings lh adt = do
--     let bn = bound_ids adt

--         -- Generates fresh names for TYPE variables, and eq function variables
--     bn' <- freshNamesN (length bn)
--     wbn <- freshNamesN (length bn)

--     let
--         bni = map (\n -> (TypeL, Id n TYPE)) bn'
--         wbni = map (\(b, f) -> (TermL , Id f (TyApp (TyConApp lh (TyFun TYPE TYPE)) (TyVar (Id b TYPE))))) $ zip bn' wbn

--         adt' = foldr (uncurry rename) adt (zip (map idName bn) bn')
    
--     return (adt', bni, wbni)

-- ---------------------------------------
-- -- Eq/Ne/Ord Function Gen
-- ---------------------------------------


-- lhEqName :: Name -> Name
-- lhEqName n = Name ("lhEqName" `T.append` nameOcc n) Nothing 0 Nothing

-- lhTEnvExpr :: Name -> Case2Alts -> LHFuncCall -> Walkers -> (Name, AlgDataTy) -> LHStateM Expr
-- lhTEnvExpr lh ca fc w (n, adt) = do
--     (adt', bni, wbni) <- boundNameBindings lh adt

--     let
--         bn' = (map (idName . snd) bni)
--         wbni' = map snd wbni
--         bfuncs = zip bn' wbni'

--     e <- lhTEnvCase ca fc w bfuncs n bn' adt'

--     return (mkLams (wbni ++ bni) e)


-- lhTEnvCase :: Case2Alts -> LHFuncCall -> Walkers -> [(Name, Id)] -> Name -> [Name] -> AlgDataTy -> LHStateM Expr
-- lhTEnvCase ca _ w ti n bn (DataTyCon {data_cons = dc}) = do
--     let t = mkTyConApp n (map (TyVar . flip Id TYPE) bn) TYPE

--     i1 <- freshIdN t
--     caseB <- freshIdN t
--     i2 <- freshIdN t

--     alts <- lhTEnvDataConAlts ca w ti n caseB i2 bn dc

--     let c = Case (Var i1) caseB alts
    
--     return (Lam TermL i1 (Lam TermL i2 c))
-- lhTEnvCase _ fc w ti _ bn (NewTyCon { rep_type = t@(TyConApp n _) }) = do
--     let t' = mkTyConApp n (map (TyVar . flip Id TYPE) bn) TYPE

--     i1 <- freshIdN t
--     i2 <- freshIdN t

--     let
--         v1 = Cast (Var i1) (t' :~ t)
--         v2 = Cast (Var i2) (t' :~ t)

--     e <- fc w ti v1 v2
    
--     return (Lam TermL i1 (Lam TermL i2 e))
-- lhTEnvCase _ _ _ _ _ _ _ = return (Var (Id (Name "BADlhTEnvCase" Nothing 0 Nothing) TyUnknown))

-- lhTEnvDataConAlts :: Case2Alts -> Walkers -> [(Name, Id)] -> Name -> Id -> Id -> [Name] -> [DataCon] -> LHStateM [Alt]
-- lhTEnvDataConAlts _ _ _ _ _ _ _ [] = return []
-- lhTEnvDataConAlts ca w ti n caseB1 i2 bn (dc@(DataCon _ t):xs) = do    
--     binds1 <- freshIdsN $ anonArgumentTypes $ PresType t
--     caseB2 <- freshIdN t

--     cAlts <- ca w ti caseB1 caseB2 binds1 dc

--     let
--         c = Case (Var i2) caseB2 cAlts
--         alt = Alt (DataAlt dc binds1) c

--     alts <- lhTEnvDataConAlts ca w ti n caseB1 i2 bn xs
    
--     return (alt:alts)

-- type Case2Alts = Walkers -> [(Name, Id)] -> Id -> Id -> [Id] -> DataCon -> LHStateM [Alt]

-- lhEqCase2Alts :: Name -> Case2Alts
-- lhEqCase2Alts lhExN w ti _ _ binds1 dc@(DataCon _ t) = do
--     binds2 <- freshIdsN $ anonArgumentTypes $ PresType t

--     true <- mkTrueE
--     false <- mkFalseE

--     -- Check that the two DataCons args are equal
--     let zbinds = zip (map Var binds1) (map Var binds2)

--     ca <- sequence $ map (uncurry (eqLHFuncCall lhExN w ti)) zbinds

--     andE <- andM
--     let e = foldr (\e' -> App (App andE e')) true ca
    
--     return ([ Alt (DataAlt dc binds2) e, Alt Default false ])

-- type LHFuncCall = Walkers -> [(Name, Id)] -> Expr -> Expr -> LHStateM Expr

-- eqLHFuncCall :: Name -> LHFuncCall
-- eqLHFuncCall lhExN w _ e e'
--     | t <- typeOf e
--     , TyConApp n _ <- tyAppCenter t
--     , ts <- tyAppArgs t
--     , Just f <- M.lookup n w =
--         let
--             as = map Type ts
--         in
--         return $ foldl' App (Var f) (as ++ [e, e'])
--     | t@(TyVar _) <- typeOf e =
--         let
--             c = App (Var (Id lhExN TyUnknown)) (Type t)
--         in
--         return $ App (App c e) e'
--     | TyFun _ _ <- typeOf e = mkTrueE
--     | TyForAll _ _ <- typeOf e = mkTrueE
--     | t <- typeOf e
--     ,  t == TyLitInt
--     || t == TyLitDouble
--     || t == TyLitFloat
--     || t == TyLitChar = do
--         b <- tyBoolT
--         let pt = TyFun t (TyFun t b)
        
--         return $ App (App (Prim Eq pt) e) e'
--     | otherwise = error $ "\nError in eqLHFuncCall " ++ show (typeOf e)

-- lhNeqName :: Name -> Name
-- lhNeqName n = Name ("lhNeName" `T.append` nameOcc n) Nothing 0 Nothing

-- lhNeqExpr :: Name -> Walkers -> Walkers -> (Name, AlgDataTy) -> LHStateM Expr
-- lhNeqExpr lh eqW _ (n, _) = do
--     meenv <- measuresM

--     let
--         f = case M.lookup n eqW of
--             Just f' -> f'
--             Nothing -> error "Unknown function in lhNeqExpr"
--         fe = case E.lookup (idName f) meenv of
--             Just fe' -> fe'
--             Nothing -> error "Unknown function def in lhNeqExpr"
--         (us, li) = unzip $ leadingLamUsesIds fe

--     no <- notM

--     let
--         nli = map idName li
    
--     li' <- doRenamesN nli li
--     let li'' = zip us li'

--     let
--         fApp = foldl' App (Var f) $ map Var $ filter (not . isTC lh) li'

--         e = mkLams li'' (App no fApp)
    
--     return e


-- isTC :: Name -> Id -> Bool
-- isTC n (Id _ (TyConApp n' _)) = n == n'
-- isTC _ _ = False

-- lhLtName :: Name -> Name
-- lhLtName n = Name ("lhLtName" `T.append` nameOcc n) Nothing 0 Nothing

-- -- Once we have the first datacon (dc1) selected, we have to branch on all datacons less than dc1
-- lhLtCase2Alts :: Name -> Walkers -> [(Name, Id)] -> Id -> Id -> [Id] -> DataCon -> LHStateM [Alt]
-- lhLtCase2Alts lhExN w ti caseB1 _ binds1 dc@(DataCon dcn _) = do
--     tenv <- typeEnv

--     true <- mkTrueE
--     false <- mkFalseE

--     let
--         tb = typeOf caseB1
--         t = tyAppCenter tb

--         adt = case t of
--                 (TyConApp n' _) -> M.lookup n' tenv
--                 _ -> error "Bad type in lhLtCase2Alts"

--         dcs = fmap (takeWhile ((/=) dcn . dataConName) . dataCon) adt

--     la <- maybeM (return []) (lhLtDCAlts true) (return dcs)

--     asame <- lhLtSameAlt lhExN w ti binds1 dc
    
--     return (Alt Default false:asame:la)

-- lhLtDCAlts :: Expr -> [DataCon] -> LHStateM [Alt]
-- lhLtDCAlts _ [] = return []
-- lhLtDCAlts true (dc@(DataCon _ t):dcs) = do
--     binds2 <- freshIdsN $ anonArgumentTypes $ PresType t

--     let alt = Alt (DataAlt dc binds2) true

--     alts <- lhLtDCAlts true dcs
    
--     return (alt:alts)

-- lhLtSameAlt :: Name -> Walkers -> [(Name, Id)] -> [Id] -> DataCon -> LHStateM Alt
-- lhLtSameAlt lhExN w ti binds1 dc@(DataCon _ t) = do    
--     binds2 <- freshIdsN $ anonArgumentTypes $ PresType t

--     let zbinds = zip (map Var binds1) (map Var binds2)

--     ltB <- sequence $ map (uncurry (ltLHFuncCall lhExN w ti)) zbinds
--     eqB <- sequence $ map (uncurry (eqLHFuncCall lhExN w ti)) zbinds

--     let zipB = zip ltB eqB

--     e <- lhLtSameAltCases zipB
    
--     return (Alt (DataAlt dc binds2) e)

-- lhLtSameAltCases :: [(Expr, Expr)] -> LHStateM Expr
-- lhLtSameAltCases [] = mkFalseE
-- lhLtSameAltCases ((lt, eq):xs) = do
--     true <- mkDCTrueM
--     false <- mkDCFalseM

--     e <- lhLtSameAltCases xs

--     b <- tyBoolT

--     [b1, b2] <- freshIdsN [b, b]

--     let c = Case lt b1 
--             [ Alt (DataAlt true []) (Data true)
--             , Alt Default 
--                 (Case eq b2 
--                     [ Alt (DataAlt true []) e
--                     , Alt Default (Data false)]
--                 )
--             ]
    
--     return c

-- ltLHFuncCall :: Name -> LHFuncCall
-- ltLHFuncCall lhExN w _ e e'
--     | t <- typeOf e
--     , TyConApp n _ <- tyAppCenter t
--     , ts <- tyAppArgs t
--     , Just f <- M.lookup n w =
--         let
--             as = map Type ts
--         in
--         return (foldl' App (Var f) (as ++ [e, e']))
--     | t@(TyVar _) <- typeOf e =
--         let
--             c = App (Var (Id lhExN TyUnknown)) (Type t)
--         in
--         return (App (App c e) e')
--     | TyFun _ _ <- typeOf e = mkTrueE
--     | TyForAll _ _ <- typeOf e = mkTrueE
--     | t <- typeOf e
--     ,  t == TyLitInt
--     || t == TyLitDouble
--     || t == TyLitFloat
--     || t == TyLitChar = do
--         b <- tyBoolT
--         let pt = TyFun t (TyFun t b)
        
--         return (App (App (Prim Lt pt) e) e')
--     | otherwise = error $ "\nError in ltLHFuncCall" ++ show (typeOf e)

-- dataConName :: DataCon -> Name
-- dataConName (DataCon n _) = n

-- lhLeName :: Name -> Name
-- lhLeName n = Name ("lhLeName" `T.append` nameOcc n) Nothing 0 Nothing

-- lhLeExpr :: Walkers -> Walkers -> Walkers -> (Name, AlgDataTy) -> LHStateM Expr
-- lhLeExpr ltW eqW _ (n, _) = do
--     eenv <- measuresM

--     let
--         lt = case M.lookup n ltW of
--             Just f' -> f'
--             Nothing -> error "Unknown function in lhLeExpr"
--         eq = case M.lookup n eqW of
--             Just f' -> f'
--             Nothing -> error "Unknown function in lhLeExpr"
--         fe = case E.lookup (idName eq) eenv of
--             Just fe' -> fe'
--             Nothing -> error "Unknown function def in lhLeExpr"
--         (us, li) = unzip $ leadingLamUsesIds fe

--     or_ex <- orM
--     li' <- freshIdsN (map typeOf li)
--     let li'' = zip us li'

--     let
--         ltApp = foldl' App (Var lt) $ map Var li'
--         eqApp = foldl' App (Var eq) $ map Var li'

--         orApp = App (App or_ex ltApp) eqApp

--         e = mkLams li'' orApp
    
--     return e

-- lhGtName :: Name -> Name
-- lhGtName n = Name ("lhGtName" `T.append` nameOcc n) Nothing 0 Nothing

-- lhGtExpr :: Walkers -> Walkers -> (Name, AlgDataTy) -> LHStateM Expr
-- lhGtExpr ltW _ (n, _) = do
--     eenv <- measuresM

--     let
--         f = case M.lookup n ltW of
--             Just f' -> f'
--             Nothing -> error "Unknown function in lhGtExpr"
--         fe = case E.lookup (idName f) eenv of
--             Just fe' -> fe'
--             Nothing -> error "Unknown function def in lhGtExpr"
--         (us, li) = unzip $ leadingLamUsesIds fe

--     li' <- freshIdsN (map typeOf li)
--     let li'' = zip us li'

--     let
--         fApp = foldl' App (Var f) $ map Var $ flipLastTwo li'

--         e = mkLams li'' fApp
    
--     return e

-- lhGeName :: Name -> Name
-- lhGeName n = Name ("lhGeName" `T.append` nameOcc n) Nothing 0 Nothing

-- lhGeExpr :: Walkers -> Walkers -> (Name, AlgDataTy) -> LHStateM Expr
-- lhGeExpr leW _ (n, _) = do
--     eenv <- measuresM

--     let
--         f = case M.lookup n leW of
--             Just f' -> f'
--             Nothing -> error "Unknown function in lhGeExpr"
--         fe = case E.lookup (idName f) eenv of
--             Just fe' -> fe'
--             Nothing -> error "Unknown function def in lhGeExpr"
--         (us, li) = unzip $ leadingLamUsesIds fe

--     li' <- freshIdsN (map typeOf li)
--     let li'' = zip us li'

--     let
--         fApp = foldl' App (Var f) $ map Var $ flipLastTwo li'

--         e = mkLams li'' fApp
    
--     return e

-- flipLastTwo :: [a] -> [a]
-- flipLastTwo (x:y:[]) = y:[x]
-- flipLastTwo (x:xs) = x:flipLastTwo xs
-- flipLastTwo xs = xs

-- ---------------------------------------
-- -- DataType Ref Gen
-- ---------------------------------------
-- lhPolyPredName :: Name -> Name
-- lhPolyPredName n = Name ("lhPolyPred" `T.append` nameOcc n) Nothing 0 Nothing

-- lhPolyPred :: Name -> Walkers -> (Name, AlgDataTy) -> LHStateM Expr
-- lhPolyPred lh w (n, adt) = do
--     (adt', bni, _) <- boundNameBindings lh adt

--     let bn = map (idName . snd) bni
    
--     tb <- tyBoolT
--     fbi <- freshIdsN (map (\(_, i) -> TyFun (TyVar i) tb) bni)
--     let fbi' = map ((,) TermL) fbi

--     let bnf = zip bn fbi

--     e <- lhPolyPredCase w n adt' bn bnf

--     return (mkLams (bni ++ fbi') e)

-- lhPolyPredCase :: Walkers -> Name -> AlgDataTy -> [Name] -> [(Name, Id)] -> LHStateM Expr
-- lhPolyPredCase w n (DataTyCon { data_cons = dc }) bn bnf = do
--     let t = mkTyConApp n (map (TyVar . flip Id TYPE) bn) TYPE

--     i1 <- freshIdN t
--     caseB <- freshIdN t

--     alts <- lhPolyPredAlts w dc bnf

--     let c = Case (Var i1) caseB alts
    
--     return (Lam TermL i1 c)
-- lhPolyPredCase w n (NewTyCon { rep_type = t }) bn bnf = do
--     let t' = mkTyConApp n (map (TyVar . flip Id TYPE) bn) TYPE

--     i <- freshIdN t'
--     caseB <- freshIdN t

--     true <- mkTrueE

--     let
--         cast = Cast (Var i) (t' :~ t)

--         e = polyPredLHFuncCall true w bnf (Var caseB)

--         alt = Alt Default e

--         c = Case cast caseB [alt]
    
--     return (Lam TermL i c)
-- lhPolyPredCase _ _ _ _ _ = error "lhPolyPredCase: Unhandled AlgDataTy"

-- lhPolyPredAlts :: Walkers -> [DataCon] -> [(Name, Id)] -> LHStateM [Alt]
-- lhPolyPredAlts _ [] _ = return []
-- lhPolyPredAlts w (dc@(DataCon _ t):dcs) bnf = do
--     binds <- freshIdsN $ anonArgumentTypes $ PresType t
        
--     e <- lhPolyPredCaseExpr w binds bnf

--     let alt = Alt (DataAlt dc binds) e

--     alts <- lhPolyPredAlts w dcs bnf
    
--     return (alt:alts)

-- lhPolyPredCaseExpr :: Walkers -> [Id] -> [(Name, Id)] -> LHStateM Expr
-- lhPolyPredCaseExpr w bn bnf = do
--     let
--         tyvs = filter (isTyVar . typeOf) bn

--         pc = map (predCalls bnf) tyvs 
    
--     an <- andM
--     true <- mkTrueE

--     let fs = map (polyPredLHFuncCall true w bnf . Var) $ filter (not . isTyVar . typeOf) bn
    
--     return $ foldr (\e -> App (App an e)) true $ pc ++ fs

-- predCalls :: [(Name, Id)] -> Id -> Expr
-- predCalls bnf i@(Id _ (TyVar tvi)) =
--     let
--         fi = lookup (idName tvi) bnf
--     in
--     case fi of
--         Just fi' -> App (Var fi') (Var i)
--         Nothing -> error $ "No function found in predCalls " ++ show i ++ "\n" ++ show bnf
-- predCalls _ _ = error "predCalls: Unhandled Type"

-- polyPredLHFuncCall :: Expr -> Walkers -> [(Name, Id)] -> Expr -> Expr
-- polyPredLHFuncCall true w bnf i = App (polyPredLHFunc' true w bnf i) i

-- polyPredLHFunc' :: Typed t => Expr -> Walkers -> [(Name, Id)] -> t -> Expr
-- polyPredLHFunc' true w bnf i
--     | t <- typeOf i
--     , TyConApp n _ <- tyAppCenter t
--     , ts <- tyAppArgs t
--     , Just f <- M.lookup n w =
--         let
--             as = map Type ts
--             as' = map (polyPredFunc' true w bnf) ts
--         in
--         foldl' App (Var f) (as ++ as')
--     | TyForAll _ _ <- typeOf i = Lam TypeL (Id (Name "nonused_id" Nothing 0 Nothing) (typeOf i)) true
--     | TyFun _ _ <- typeOf i = Lam TermL (Id (Name "nonused_id" Nothing 0 Nothing) (typeOf i)) true
--     | t <- typeOf i
--     ,  t == TyLitInt
--     || t == TyLitDouble
--     || t == TyLitFloat
--     || t == TyLitChar = Lam TermL (Id (Name "nonused_id" Nothing 0 Nothing) (typeOf i)) true
--     | TyVar _ <- typeOf i = polyPredFunc' true w bnf (typeOf i)
--     | TyApp _ _ <- typeOf i =
--         Lam TermL (Id (Name "nonused_id" Nothing 0 Nothing) (typeOf i)) true
--     | otherwise = error $ "Unhandled type in polyPredLHFunc' " ++ show (typeOf i)

-- polyPredFunc' :: Expr ->  Walkers -> [(Name, Id)] -> Type -> Expr
-- polyPredFunc' _ _ bnf (TyVar (Id n _)) 
--     | Just tyF <- lookup n bnf = 
--         Var tyF
-- polyPredFunc' true w bnf t
--     | TyConApp n _ <- tyAppCenter t
--     , ts <- tyAppArgs t
--     ,Just f <- M.lookup n w =
--         let
--             as = map Type ts
--             ft = map (polyPredLHFunc' true w bnf . PresType) ts
--         in
--         foldl' App (Var f) (as ++ ft)
-- polyPredFunc' _ _ _ _ = error "polyPredFunc': Unhandled type'"

-- createPrimFuncs :: Walkers -> Primitive -> [Name] -> LHStateM Walkers
-- createPrimFuncs w _ [] = return w
-- createPrimFuncs w p (n:ns) = do
--     w' <- createPrimFunc w p n
    
--     createPrimFuncs w' p ns

-- createPrimFunc :: Walkers -> Primitive -> Name -> LHStateM Walkers
-- createPrimFunc w p n = do
--     f <- freshSeededStringN "prim"

--     let e = Prim p TyBottom
--     insertMeasureM f e

--     let w2 = M.insert n (Id f TyBottom) w
    
--     return w2

-- createPrimPolyPreds :: Walkers -> [Name] -> LHStateM Walkers
-- createPrimPolyPreds w [] = return w
-- createPrimPolyPreds w (n:ns) = do
--     w' <- createPrimPolyPred w n
    
--     createPrimPolyPreds w' ns

-- createPrimPolyPred :: Walkers -> Name -> LHStateM Walkers
-- createPrimPolyPred w n = do
--     f <- freshSeededStringN "primPP"

--     let i = Id (Name "x" Nothing 0 Nothing) TyBottom
--     let e = Lam TermL i (Var i)
--     insertMeasureM f e

--     let w2 = M.insert n (Id f TyBottom) w
    
--     return w2