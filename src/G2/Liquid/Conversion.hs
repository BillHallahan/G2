{-# LANGUAGE CPP, FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Conversion ( LHDictMap
                            , DictMaps (..)
                            , BoundTypes
                            , CheckPre (..)
                            , mergeLHSpecState
                            , convertSpecType
                            , dictMapFromIds
                            , convertLHExpr
                            , specTypeToType
                            , unsafeSpecTypeToType
                            , symbolName
                            , lhTCDict'

                            , higherOrderTickName) where

import G2.Language
import qualified G2.Language.KnownValues as KV
import G2.Language.Monad
import qualified G2.Language.ExprEnv as E
import G2.Language.TypeEnv
import G2.Liquid.Types
import G2.Translation.Haskell

#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
import qualified GHC.Types.Var as Var
#else
import qualified Var as Var
#endif

import Language.Fixpoint.Types.Names
import Language.Fixpoint.Types.Sorts
import qualified Language.Fixpoint.Types.Refinements as Ref
import Language.Fixpoint.Types.Refinements hiding (Expr, I)
import Language.Haskell.Liquid.Types

import Data.Coerce
import Data.Foldable
import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T
import qualified G2.Language.TyVarEnv as TV 

-- | A mapping of TyVar Name's, to Id's for the LH dict's
type LHDictMap = HM.HashMap Name Id

-- | A mapping of TyVar Name's, to Id's for the Num dict's
type NumDictMap = HM.HashMap Name Id

-- | A mapping of TyVar Name's, to Id's for the Integral dict's
type IntegralDictMap = HM.HashMap Name Id

-- | A mapping of TyVar Name's, to Id's for the Fractional dict's
type FractionalDictMap = HM.HashMap Name Id

-- | A mapping of TyVar Name's, to Id's for the Ord dict's
type OrdDictMap = HM.HashMap Name Id

-- | A collection of all DictMaps required to convert LH refinement types to G2 `Expr`@s@
data DictMaps = DictMaps { lh_dicts :: LHDictMap
                         , num_dicts :: NumDictMap
                         , integral_dicts :: IntegralDictMap
                         , fractional_dicts :: FractionalDictMap
                         , ord_dicts :: OrdDictMap } deriving (Eq, Show, Read)

copyIds :: Name -> Name -> DictMaps -> DictMaps
copyIds n1 n2 dm@(DictMaps { lh_dicts = lhd
                           , num_dicts = nd
                           , integral_dicts = ind
                           , fractional_dicts = frac
                           , ord_dicts = od }) =
    let
        dm2 = case HM.lookup n1 lhd of
                Just lh -> dm { lh_dicts = HM.insert n2 lh lhd }
                Nothing -> dm

        dm3 = case HM.lookup n1 nd of
                Just num -> dm2 { num_dicts = HM.insert n2 num nd }
                Nothing -> dm2

        dm4 = case HM.lookup n1 ind of
                Just int -> dm3 { integral_dicts = HM.insert n2 int ind }
                Nothing -> dm3

        dm5 = case HM.lookup n1 frac of
                Just fr -> dm4 { fractional_dicts = HM.insert n2 fr frac }
                Nothing -> dm4

        dm6 = case HM.lookup n1 od of
                Just ord -> dm5 { ord_dicts = HM.insert n2 ord od }
                Nothing -> dm5
    in
    dm6

-- | A mapping of variable names to the corresponding types
type BoundTypes = HM.HashMap Name Type

type NMExprEnv = HM.HashMap (T.Text, Maybe T.Text) (Name, Expr)

mergeLHSpecState :: TV.TyVarEnv -> [(Var.Var, LocSpecType)] -> LHStateM ()
mergeLHSpecState tv var_st = do
    eenv <- exprEnv
    let nm_eenv = E.nameModMap eenv
    mapM_ (uncurry (mergeLHSpecState' tv nm_eenv)) var_st

mergeLHSpecState' :: TV.TyVarEnv -> NMExprEnv -> Var.Var -> LocSpecType -> LHStateM ()
mergeLHSpecState' tv nm_eenv v lst = do
    let
        (Id (Name n m _ _) _) = mkIdUnsafe v
        g2N = HM.lookup (n, m) nm_eenv

    case g2N of
        Just (n', e) -> do
            case convertVar n' of
                True -> do
                    e' <- mergeSpecType tv (val lst) n' e
                    insertE n' e'

                    assumpt <- createAssumption tv (val lst) e
                    insertAssumptionM n' assumpt

                    post <- createPost tv (val lst) e
                    insertPostM n' post
                False -> return ()
        Nothing -> return ()

convertVar :: Name -> Bool
convertVar (Name "fromInteger" _ _ _) = False
convertVar (Name "error" _ _ _) = False
convertVar (Name "patError" _ _ _) = False
convertVar (Name "." _ _ _) = False
convertVar _ = True

mergeSpecType :: TV.TyVarEnv -> SpecType -> Name -> Expr -> LHStateM Expr
mergeSpecType tv st fn e = do
    lh <- lhTCM

    -- Create new bindings to use in the Ref. Type
    let argT = spArgumentTypes $ typeOf tv e
    is <- mapM argsFromArgT argT
    let lu = map argTypeToLamUse argT

    -- Gather up LH TC's to use in Assertion
    dm@(DictMaps {lh_dicts = lhm}) <- dictMapFromIds tv is

    trueE <- mkTrueE
    higher_is <- handleHigherOrderSpecs tv CheckPre (mkHigherAssert trueE) lh dm (HM.map (typeOf tv) lhm) is st

    let e' = foldl' App e . map (\(i, hi) -> maybe (Var i) id hi) $ zip is higher_is

    -- Create a variable for the returned value
    -- We do not pass the LH TC to the assertion, since there is no matching
    -- lambda for it in the LH Spec
    r <- freshIdN (typeOf tv e')
    let is' = filter (not . isTC lh . (typeOf tv)) is
    assert <- convertAssertSpecType tv dm (HM.map (typeOf tv) lhm) is' r st

    let fc = FuncCall { funcName = fn 
                      , arguments = map Var is
                      , returns = Var r }
        e'' = modifyASTs (repAssertFC fc) e'
    let rLet = Let [(r, e'')] $ Assert (Just fc) assert (Var r)
    
    let e''' = foldr (uncurry Lam) rLet $ zip lu is

    return e'''
    where
        -- We insert an extra, redundant assume to record information about the function being used as a higher order function
        mkHigherAssert true_dc spec i ars ret =
            Tick (NamedLoc higherOrderTickName) . Assume (Just $ FuncCall { funcName = idName i, arguments = map Var ars, returns = Var ret }) true_dc $ Assert Nothing spec (Var ret)

        repAssertFC fc_ (Assert Nothing e1 e2) = Assert (Just fc_) e1 e2
        repAssertFC _ e_ = e_

createAssumption :: TV.TyVarEnv -> SpecType -> Expr -> LHStateM ([(LamUse, Id)], [Maybe Expr], Expr)
createAssumption tv st e = do
    lh <- lhTCM

    -- Create new bindings to use in the Ref. Type
    let argT = spArgumentTypes $ typeOf tv e
    is <- mapM argsFromArgT argT
    let lu = map argTypeToLamUse argT

    let is' = filter (not . isTC lh . (typeOf tv)) is
    dm@(DictMaps {lh_dicts = lhm}) <- dictMapFromIds tv is

    assume <- convertAssumeSpecType tv dm (HM.map (typeOf tv)lhm) is' st
    higher_is <- handleHigherOrderSpecs tv CheckOnlyPost mkHigherAssume lh dm (HM.map (typeOf tv) lhm) is st

    let assume' = foldr (uncurry Lam) assume $ zip lu is
    return (zip lu is, higher_is, assume')
    where
        mkHigherAssume spec i ars ret =
            Tick (NamedLoc higherOrderTickName) $ Assume (Just $ FuncCall { funcName = idName i, arguments = map Var ars, returns = Var ret } ) spec (Var ret)

higherOrderTickName :: Name
higherOrderTickName = Name "HIGHER_ORDER_FUNC" Nothing 0 Nothing

createPost :: TV.TyVarEnv -> SpecType -> Expr -> LHStateM Expr
createPost tv st e = do
    lh <- lhTCM

    -- Create new bindings to use in the Ref. Type
    let argT = spArgumentTypes $ typeOf tv e
    is <- mapM argsFromArgT argT
    let lu = map argTypeToLamUse argT

    r <- freshIdN (returnType $ typeOf tv e)
    let is' = filter (not . isTC lh . (typeOf tv) ) is
    dm@(DictMaps {lh_dicts = lhm}) <- dictMapFromIds tv is

    pst <- convertPostSpecType tv dm (HM.map (typeOf tv) lhm) is' r st

    return . foldr (uncurry Lam) pst $ zip (lu ++ [TermL]) (is ++ [r])



dictMapFromIds :: TV.TyVarEnv -> [Id] -> LHStateM DictMaps
dictMapFromIds tv is = do
    lh <- lhTCM
    num <- lhNumTCM
    int <- return . KV.integralTC =<< knownValues
    frac <- return . KV.fractionalTC =<< knownValues
    ord <- ordTCM

    let lhm = tcWithNameMap tv lh is
    let nm = tcWithNameMap tv num is
    let im = tcWithNameMap tv int is
    let fr = tcWithNameMap tv frac is
    let om = tcWithNameMap tv ord is

    return $ DictMaps { lh_dicts = lhm
                      , num_dicts = nm
                      , integral_dicts = im
                      , fractional_dicts = fr
                      , ord_dicts = om }

isTC :: Name -> Type -> Bool
isTC n t = case tyAppCenter t of
                TyCon n' _ -> n == n'
                _ -> False

argsFromArgT :: ArgType -> LHStateM Id
argsFromArgT (AnonType t) = freshIdN t
argsFromArgT (NamedType i) = return i

-- | Should we translate the precondition in convertSpecType?
data CheckPre = CheckPre | CheckOnlyPost deriving Eq

convertAssumeSpecType :: TV.TyVarEnv -> DictMaps -> BoundTypes -> [Id] -> SpecType -> LHStateM Expr
convertAssumeSpecType tv m bt is st = do
    convertSpecType tv CheckPre m bt is Nothing st

convertAssertSpecType :: TV.TyVarEnv -> DictMaps -> BoundTypes -> [Id] -> Id -> SpecType -> LHStateM Expr
convertAssertSpecType tv m bt is r st = do
    convertSpecType tv CheckPre m bt is (Just r) st

convertPostSpecType :: TV.TyVarEnv -> DictMaps -> BoundTypes -> [Id] -> Id -> SpecType -> LHStateM Expr
convertPostSpecType tv m bt is r st =
    convertSpecType tv CheckOnlyPost m bt is (Just r) st

-- | See also: convertAssumeSpecType, convertAssertSpecType
-- We can Maybe pass an Id for the value returned by the function
-- If we do, our Expr includes the Refinement on the return value,
-- otherwise it does not.  This allows us to use this same function to
-- translate both for assumptions and assertions
convertSpecType :: TV.TyVarEnv -> CheckPre -> DictMaps -> BoundTypes -> [Id] -> Maybe Id -> SpecType -> LHStateM Expr
convertSpecType tv _ m bt _ r (RVar {rt_var = (RTV v), rt_reft = ref})
    | Just r' <- r = do
        let symb = reftSymbol $ ur_reft ref
        let i = mkIdUnsafe v

        let symbId = convertSymbolT symb (TyVar i)

        let bt' = HM.insert (idName symbId) (typeOf tv symbId) bt

        re <- convertLHExpr tv m bt' Nothing (reftExpr $ ur_reft ref)

        return $ App (Lam TermL symbId re) (Var r')
    | otherwise = mkTrueE
convertSpecType tv cp m bt (i:is) r (RFun {rt_bind = b, rt_in = fin, rt_out = fout }) = do
    t <- unsafeSpecTypeToType tv fin
    let i' = convertSymbolT b t

    let bt' = HM.insert (idName i') t bt

    e <- convertSpecType tv cp m bt' is r fout

    case hasFuncType (typeOf tv i) of
        True -> return $ App (Lam TermL i' e) (Var i)
        False -> do
            e' <- convertSpecType tv cp m bt' [] (Just i') fin
            an <- lhAndE
            let e'' = if cp == CheckPre
                            then App (App an e') e
                            else e
            
            return $ App (Lam TermL i' e'') (Var i)
convertSpecType tv cp m bt (i:is) r (RAllT {rt_tvbind = RTVar (RTV v) _, rt_ty = rty}) = do
    let i' = mkIdUnsafe v


    let m' = copyIds (idName i) (idName i') m
    let bt' = HM.insert (idName i') (typeOf tv i) bt

    e <- convertSpecType tv cp m' bt' is r rty
    return $ App (Lam TypeL i' e) (Var i)
convertSpecType tv cp m bt _ r (RApp {rt_tycon = c, rt_reft = ref, rt_args = as})
    | Just r' <- r = do
        let symb = reftSymbol $ ur_reft ref
        ty <- return . maybe (error "Error in convertSpecType") id =<< rTyConType tv c as
        let i = convertSymbolT symb ty

        let bt' = HM.insert (idName i) ty bt

        argsPred <- polyPredFunc tv cp as ty m bt' r'
        re <- convertLHExpr tv m bt' Nothing (reftExpr $ ur_reft ref)

        an <- lhAndE

        return $ App (App an (App (Lam TermL i re) (Var r'))) argsPred
    | otherwise = mkTrueE
convertSpecType _ _ _ _ _ _ (RAppTy { }) = mkTrueE
convertSpecType _ _ _ _ _ _ st@(RFun {}) = error $ "RFun " ++ show st
convertSpecType _ _ _ _ _ _ st@(RAllT {}) = error $ "RAllT " ++ show st
convertSpecType _ _ _ _ _ _ st@(RAllP {}) = error $ "RAllP " ++ show st
convertSpecType _ _ _ _ _ _ st@(RAllE {}) = error $ "RAllE " ++ show st
convertSpecType _ _ _ _ _ _ st@(REx {}) = error $ "REx " ++ show st
convertSpecType _ _ _ _ _ _ st@(RExprArg {}) = error $ "RExprArg " ++ show st
convertSpecType _ _ _ _ _ _ st@(RRTy {}) = error $ "RRTy " ++ show st
convertSpecType _ _ _ _ _ _ st = error $ "Bad st = " ++ show st

handleHigherOrderSpecs :: TV.TyVarEnv -> CheckPre -> (Expr -> Id -> [Id] -> Id -> Expr) -> Name -> DictMaps -> BoundTypes -> [Id] -> SpecType -> LHStateM [Maybe Expr]
handleHigherOrderSpecs tv check_pre wrap_spec lh dm bt (i:is) st | isTC lh $ typeOf tv i = do
    es <- handleHigherOrderSpecs tv check_pre wrap_spec lh dm bt is st
    return $ Nothing:es
handleHigherOrderSpecs tv check_pre wrap_spec lh dm bt (i:is) (RFun {rt_bind = b, rt_in = fin, rt_out = fout })
    | hasFuncType (typeOf tv i) = do
        t <- unsafeSpecTypeToType tv fin
        let i' = convertSymbolT b t

        let bt' = HM.insert (idName i') t bt
        es <- handleHigherOrderSpecs tv check_pre wrap_spec lh dm bt' is fout

        ars <- freshIdsN (anonArgumentTypes $ typeOf tv i)
        ret <- freshIdN (returnType $ typeOf tv i)
        spec <- convertSpecType tv check_pre dm bt' ars (Just ret) fin

        let let_assert_spec = mkLams (zip (repeat TermL) ars)
                            . Let [(ret, mkApp $ Var i:map Var ars)]
                            $ wrap_spec spec i ars ret -- (Var ret)

        return $ Just let_assert_spec:es
    | otherwise = do
        t <- unsafeSpecTypeToType tv fin
        let i' = convertSymbolT b t

        let bt' = HM.insert (idName i') t bt
        es <- handleHigherOrderSpecs tv check_pre wrap_spec lh dm bt' is fout
        return $ Nothing:es
handleHigherOrderSpecs _ _ _ _ _ _ [] _ = return []
handleHigherOrderSpecs tv check_pre wrap_spec lh dm bt (i:is) (RAllT {rt_tvbind = RTVar (RTV v) _, rt_ty = rty}) = do
    let i' = mkIdUnsafe v

    let dm' = copyIds (idName i) (idName i') dm
    let bt' = HM.insert (idName i') (typeOf tv i) bt

    es <- handleHigherOrderSpecs tv check_pre wrap_spec lh dm' bt' is rty
    return $ Nothing:es
handleHigherOrderSpecs _ _ _ _ _ _ _ _ = error "handleHigherOrderSpecs: unhandled SpecType"

polyPredFunc :: TV.TyVarEnv -> CheckPre -> [SpecType] -> Type -> DictMaps -> BoundTypes -> Id -> LHStateM Expr
polyPredFunc tv cp as ty m bt b = do
    dict <- lhTCDict m ty
    as' <- mapM (polyPredLam tv cp m bt) as

    bool <- tyBoolT

    let ar1 = Type (typeOf tv b)
        ars = [dict] ++ as' ++ [Var b]
        t = TyForAll b $ foldr1 TyFun $ map (typeOf tv) ars ++ [bool]

    lhPP <- lhPPM
    
    return $ mkApp $ Var (Id lhPP t):ar1:ars

polyPredLam :: TV.TyVarEnv -> CheckPre -> DictMaps -> BoundTypes -> SpecType -> LHStateM Expr
polyPredLam tv cp m bt rapp  = do
    t <- unsafeSpecTypeToType tv rapp

    let argT = spArgumentTypes $ t
    is <- mapM argsFromArgT argT

    i <- freshIdN . returnType $ t
    
    st <- convertSpecType tv cp m bt is (Just i) rapp
    return $ Lam TermL i st

convertLHExpr :: TV.TyVarEnv -> DictMaps -> BoundTypes -> Maybe Type -> Ref.Expr -> LHStateM Expr
convertLHExpr _ _ _ t (ECon c) = convertCon t c
convertLHExpr tv _ bt t (EVar s) = convertEVar tv (symbolName s) bt t
convertLHExpr tv m bt rt eapp@(EApp e e') = do
    meas <- measuresM
    m_set_e <- convertSetExpr tv meas m bt rt eapp
    
    case m_set_e of
        Just set_e -> return set_e
        Nothing -> do
            f <- convertLHExpr tv m bt Nothing e

            let at = argumentTypes $ typeOf tv f
                f_ar_t = case at of
                            (_:_) -> Just $ last at
                            _ -> Nothing

                f_ar_ts = fmap relTyVars f_ar_t

            argE <- convertLHExpr tv m bt f_ar_t e'

            let tArgE = typeOf tv argE
                ctArgE = tyAppCenter tArgE
                ts = take (numTypeArgs $ typeOf tv f) $ relTyVars tArgE

            case (ctArgE, f_ar_ts) of
                (_, Just f_ar_ts') -> do
                    let specTo = concatMap (map snd) $ map TV.toList $ map (fromJust . uncurry specializes) $ zip ts f_ar_ts'
                        te = map Type specTo

                    tcs <- mapM (lhTCDict m) ts

                    let fw = mkApp $ f:te

                        apps = mkApp $ fw:tcs ++ [argE]
                    
                    return apps
                _ -> return $ App f argE
    where
        relTyVars t@(TyVar _) = [t]
        relTyVars t@(TyApp _ _) = tyAppArgs t
        relTyVars _ = []
convertLHExpr tv m bt t (ENeg e) = do
    e' <- convertLHExpr tv m bt t e
    let t' = typeOf tv e'

    neg <- lhNegateM
    num <- lhNumTCM
    a <- freshIdN TYPE
    let tva = TyVar a
    let negate' = Var $ Id neg 
                        (TyForAll a
                            (TyFun
                                (TyApp (TyCon num (TyFun TYPE TYPE)) tva)
                                (TyFun
                                    tva
                                    tva
                                )
                            )
                        )

    nDict <- numDict m t'

    return $ mkApp [ negate'
                   , Type t'
                   , nDict
                   , e' ]
convertLHExpr tv m bt t (EBin b e e') = do
    (e2, e2') <- correctTypes tv m bt t e e'
    b' <- convertBop b

    let t' = typeOf tv e2

    nDict <- bopTCDict b m t'

    return $ mkApp [ b'
                   , Type t'
                   , nDict
                   , e2
                   , e2' ]
convertLHExpr tv m bt t (EIte b e e') = do
    b2 <- convertLHExpr tv m bt t b
    (e2, e2') <- correctTypes tv m bt t e e'

    trueDC <- mkDCTrueM
    falseDC <- mkDCFalseM

    bnd <- freshIdN =<< tyBoolT

    return $ Case b2 bnd (typeOf tv e2) [Alt (DataAlt trueDC []) e2, Alt (DataAlt falseDC []) e2']
convertLHExpr tv m bt _ (ECst e s) = do
    t <- sortToType s
    convertLHExpr tv m bt (Just t) e
convertLHExpr tv m bt _ (PAnd es) = do
    es' <- mapM (convertLHExpr tv m bt Nothing) es

    trueE <- mkTrueE
    an <- lhAndE

    case es' of
        [] -> return $ trueE
        [e] -> return e
        _ -> return $ foldr (\e -> App (App an e)) trueE es'
convertLHExpr tv m bt _ (POr es) = do
    es' <- mapM (convertLHExpr tv m bt Nothing) es

    false <- mkFalseE
    orE <- lhOrE

    case es' of
        [] -> return false
        [e] -> return e
        _ -> return $ foldr (\e -> App (App orE e)) false es'
convertLHExpr tv m bt _ (PNot e) = do
    e' <- convertLHExpr tv m bt Nothing e
    no <- notM
    return (App no e') 
convertLHExpr tv m bt t (PImp e1 e2) = do
    e1' <- convertLHExpr tv m bt t e1
    e2' <- convertLHExpr tv m bt t e2
    imp <- mkImpliesE
    return $ mkApp [imp, e1', e2']
convertLHExpr tv m bt t (PIff e1 e2) = do
    e1' <- convertLHExpr tv m bt t e1
    e2' <- convertLHExpr tv m bt t e2
    iff <- iffM
    return $ mkApp [iff, e1', e2']
convertLHExpr tv m bt _ (PAtom brel e1 e2) = do
    (e1', e2') <- correctTypes tv m bt Nothing e1 e2
    brel' <- convertBrel brel

    let t' = typeOf tv e1'

    dict <- brelTCDict m t'

    return $ mkApp [brel', Type t', dict, e1', e2']
convertLHExpr _ _ _ _ e = error $ "Untranslated LH Expr " ++ (show e)

convertSetExpr :: TV.TyVarEnv -> Measures -> DictMaps -> BoundTypes -> Maybe Type -> Ref.Expr -> LHStateM (Maybe Expr)
convertSetExpr tv meas dm bt rt e
    | [EVar v, e1] <- unEApp e
    , Just (nm, nm_mod) <- get_nameTyVarAr v
    , Just (f_nm, f_e) <- E.lookupNameMod nm nm_mod meas = do
        e1' <- convertLHExpr tv dm bt rt e1
        tyI <- tyIntegerT
        t <- if typeOf tv e1' == tyI then tyIntT else return $ typeOf tv e1'
        e1'' <- if typeOf tv e1' == tyI then correctType tv dm t e1' else return e1'
        return . Just $ mkApp ([ Var (Id f_nm (typeOf tv f_e))
                               , Type t
                               , e1''])
    | [EVar v, e1, e2] <- unEApp e
    , Just (nm, nm_mod) <- get_nameTyVarArOrd v
    , Just (f_nm, f_e) <- E.lookupNameMod nm nm_mod meas = do
        e1' <- convertLHExpr tv dm bt rt e1
        e2' <- convertLHExpr tv dm bt rt e2
        let TyApp _ t2 = typeOf tv e2'
        e1'' <- correctType tv dm t2 e1'
        let t = typeOf tv e1''
        ord <- ordDict dm t
        return . Just $ mkApp ([ Var (Id f_nm (typeOf tv f_e))
                               , Type t
                               , ord
                               , e1''
                               , e2' ])
    | EVar v:es <- unEApp e
    , Just (nm, nm_mod) <- get_nameSetAr v
    , Just (f_nm, f_e) <- E.lookupNameMod nm nm_mod meas = do
        es' <- mapM (convertLHExpr tv dm bt rt) es
        case typeOf tv (head es') of
            TyApp _ t -> do
                return . Just $ mkApp ([ Var (Id f_nm (typeOf tv f_e))
                                       , Type t ]
                                        ++ es')
            _ -> do
                t <- tyIntT
                return . Just $ App (Var (Id f_nm (typeOf tv f_e))) (Type t)
    | EVar v:es <- unEApp e
    , Just (nm, nm_mod) <- get_nameSetArOrd v
    , Just (f_nm, f_e) <- E.lookupNameMod nm nm_mod meas = do
        es' <- mapM (convertLHExpr tv dm bt rt) es
        case typeOf tv (head es') of
            TyApp _ t -> do
                ord <- ordDict dm t
                return . Just $ mkApp ([ Var (Id f_nm (typeOf tv f_e))
                                       , Type t
                                       , ord ]
                                        ++ es')
            _ -> error "convertSetExpr: incorrect type"
    | otherwise = return Nothing
    where
        get_nameTyVarAr v = case nameOcc (symbolName v) of
                            "Set_sng" -> Just ("singleton", Just "Data.Set.Internal")
                            _ -> Nothing

        get_nameTyVarArOrd v = case nameOcc (symbolName v) of
                            "Set_mem" -> Just ("member", Just "Data.Set.Internal")
                            _ -> Nothing

        get_nameSetAr v = case nameOcc (symbolName v) of
                            "Set_empty" -> Just ("empty", Just "Data.Set.Internal")
                            "Set_emp" -> Just ("null", Just "Data.Set.Internal")
                            _ -> Nothing

        get_nameSetArOrd v = case nameOcc (symbolName v) of
                            "Set_cup" -> Just ("union", Just "Data.Set.Internal")
                            "Set_cap" -> Just ("intersection", Just "Data.Set.Internal")
                            "Set_sub" -> Just ("isSubsetOf", Just "Data.Set.Internal")
                            _ -> Nothing

unEApp :: Ref.Expr -> [Ref.Expr]
unEApp (EApp f a) = unEApp f ++ [a]
unEApp e = [e]

convertBop :: Bop -> LHStateM Expr
convertBop Ref.Plus = convertBop' lhPlusM
convertBop Ref.Minus = convertBop' lhMinusM
convertBop Ref.Times = convertBop' lhTimesM
convertBop Ref.Div = convertBop' lhDivM
convertBop Ref.Mod = convertBop' lhModM
convertBop Ref.RTimes = convertBop' lhTimesM
convertBop Ref.RDiv = convertBop' lhDivM

convertBop' :: LHStateM Name -> LHStateM Expr
convertBop' f = do
    num <- lhNumTCM
    n <- f
    a <- freshIdN TYPE
    let tva = TyVar a
    return $ Var $ Id n (TyForAll a
                            (TyFun
                                (TyApp (TyCon num (TyFun TYPE TYPE)) tva)
                                (TyFun
                                    tva
                                    (TyFun 
                                        tva 
                                        tva
                                    )
                                )
                            )
                            
                        )

-- | We often end up in the situation of having to compare some value of type a1
-- to an instance of type Integer.  This function, in order:
-- (1) Converts the value of type Integer to the type a1, if a1 is an instance
--     of Num.
-- (2) Converts the value of type a1 to Integer, if a1 is not an instance of Num
-- but is a value of type Integral
-- (3) Fails with an error.
correctTypes :: TV.TyVarEnv -> DictMaps -> BoundTypes -> Maybe Type -> Ref.Expr -> Ref.Expr -> LHStateM (Expr, Expr)
correctTypes tv m bt mt re re' = do
    fIntgr <- lhFromIntegerM
    tIntgr <- lhToIntegerM
    tyI <- tyIntegerT

    e <- convertLHExpr tv m bt mt re
    e' <- convertLHExpr tv m bt mt re'

    let t = typeOf tv e
    let t' = typeOf tv e'

    let retT = returnType $ typeOf tv e
    let retT' = returnType $ typeOf tv e'

    may_nDict <- maybeNumDict m retT
    may_nDict' <- maybeNumDict m retT'

    may_iDict <- maybeIntegralDict m retT
    may_iDict' <- maybeIntegralDict m retT'

    may_fDict <- maybeFractionalDict m retT
    may_fDict' <- maybeFractionalDict m retT'

    may_ratio_e <- maybeRatioFromInteger tv m e
    may_ratio_e' <- maybeRatioFromInteger tv m e'
    fromRationalF <- lhFromRationalM

    if | t == t' -> return (e, e')
       | retT /= tyI
       , retT' == tyI
       , Just nDict <- may_nDict -> return (e, mkApp [Var fIntgr, Type t, nDict, e'])

       | retT == tyI
       , retT' /= tyI
       , Just nDict' <- may_nDict' -> return (mkApp [Var fIntgr, Type t', nDict', e], e')

       | retT /= tyI
       , retT' == tyI
       , Just iDict <- may_iDict -> return (mkApp [Var tIntgr, Type t, iDict, e], e')

       | retT == tyI
       , retT' /= tyI
       , Just iDict' <- may_iDict' -> return (e, mkApp [Var tIntgr, Type t', iDict', e'])

       | Just ratio_e <- may_ratio_e
       , Just fDict' <- may_fDict' -> return (mkApp [Var fromRationalF, Type t', fDict', ratio_e], e')

       | Just fDict <- may_fDict
       , Just ratio_e' <- may_ratio_e' -> return (e, mkApp [Var fromRationalF, Type t, fDict, ratio_e'])

       | Just iDict <- may_iDict
       , Just nDict' <- may_nDict' ->
            return (mkApp [Var fIntgr, Type t', nDict', mkApp [Var tIntgr, Type t, iDict, e]], e')

       | Just nDict <- may_nDict
       , Just iDict' <- may_iDict' ->
            return (e, mkApp [Var fIntgr, Type t, nDict, mkApp [Var tIntgr, Type t', iDict', e']])

       | otherwise -> error $ "correctTypes: Unhandled case"
                                ++ "\ne = " ++ show e
                                ++ "\ne' = " ++ show e'
                                ++ "\nt = " ++ show t
                                ++ "\nt' = " ++ show t'
                                ++ "\nretT = " ++ show retT
                                ++ "\nretT' = " ++ show retT'
                                ++ "\nm = " ++ show m

correctType :: TV.TyVarEnv -> DictMaps -> Type -> Expr -> LHStateM Expr
correctType tv m t e = do
    fIntgr <- lhFromIntegerM
    tyI <- tyIntegerT

    let t' = typeOf tv e

    may_nDict <- maybeNumDict m t

    if | t == t' -> return e
       | t' == tyI
       , t /= tyI
       , Just nDict <- may_nDict -> return $ mkApp [Var fIntgr, Type t, nDict, e]
       | otherwise -> error $ "correctType: unhandled case\n" ++ show e ++ "\nmay_nDict" ++ show may_nDict

maybeRatioFromInteger :: TV.TyVarEnv -> DictMaps -> Expr -> LHStateM (Maybe Expr)
maybeRatioFromInteger tv m e = do
    tyI <- tyIntegerT

    toRatioF <- lhToRatioFuncM -- return . mkToRatioExpr =<< knownValues
    may_iDict <- maybeIntegralDict m (typeOf tv e)

    dcIntegerE <- mkDCIntegerE

    if | Just iDict <- may_iDict
        , typeOf tv e == tyI  ->
            return . Just $ mkApp [Var toRatioF, Type (typeOf tv e), iDict, e, App dcIntegerE (Lit (LitInt 1))]
       | otherwise -> return Nothing

convertSymbolT :: Symbol -> Type -> Id
convertSymbolT s = Id (symbolName s)

reftSymbol :: Reft -> Symbol
reftSymbol = fst . unpackReft

reftExpr :: Reft -> Ref.Expr
reftExpr = snd . unpackReft

unpackReft :: Reft -> (Symbol, Ref.Expr) 
unpackReft = coerce

-- If possible, we split symbols at the last "." not in parenthesis, to
-- correctly set module names 
symbolName :: Symbol -> Name
symbolName s =
    let
        t = symbolSafeText s
        l = case T.null t of
            True -> Just $ T.last t
            False -> Nothing

        ((m, n), i) =
            case l of
                Just ')' -> (T.breakOnEnd ".(" t, 2)
                _ -> (T.breakOnEnd "." t, 1)

        m' = T.dropEnd i m
    in
    case (m', n) of
        (n', "") -> Name n' Nothing 0 Nothing
        _ -> Name n (Just m') 0 Nothing

convertEVar :: TV.TyVarEnv -> Name -> BoundTypes -> Maybe Type -> LHStateM Expr
convertEVar tv nm@(Name n md _ _) bt mt
    | Just t <- HM.lookup nm bt = return $ Var (Id nm t)
    | otherwise = do
        meas <- measuresM
        tenv <- typeEnv
        
        if | Just (n', e) <- E.lookupNameMod n md meas ->
                return . Var $ Id n' (typeOf tv e)
           | Just dc <- getDataConNameMod' tenv nm -> return $ Data dc
           | Just t <- mt -> return $ Var (Id nm t)
           | otherwise -> error $ "convertEVar: Required type not found" ++ "\n" ++ show n ++ "\nbt = " ++ show bt
    where
        getDataConNameMod' tenv n = find (flip dataConHasNameMod n) $ concatMap dataCon $ HM.elems tenv
        dataConHasNameMod (DataCon (Name n m _ _) _ _ _) (Name n' m' _ _) = n == n' && m == m'


convertCon :: Maybe Type -> Constant -> LHStateM Expr
convertCon (Just (TyCon n _)) (Ref.I i) = do
    tyI <- tyIntT
    case tyI of
        TyCon ti _ -> do
            dc <- mkDCIntE
            if n == ti
                then return $ App dc (Lit . LitInt $ fromIntegral i)
                else error $ "Unknown Con" ++ show n
        _ -> error "convertCon: Non-tyInt"
convertCon _ (Ref.I i) = do
    dc <- mkDCIntegerE
    return $ App dc (Lit . LitInt $ fromIntegral i)
convertCon _ (Ref.R d) = do
    dc <- mkDCDoubleE
    return $ App dc (Lit $ LitDouble d)
convertCon _ _ = error "convertCon: Unhandled case"

unsafeSpecTypeToType :: TV.TyVarEnv -> SpecType -> LHStateM Type
unsafeSpecTypeToType tv st = do
    t' <- specTypeToType tv st
    case t' of
        Just t'' -> return t''
        Nothing -> error $ "Unhandled SpecType" ++ show st

specTypeToType :: TV.TyVarEnv -> SpecType -> LHStateM (Maybe Type)
specTypeToType _ (RVar {rt_var = (RTV v)}) = do
    let i = mkIdUnsafe v
    return $ Just (TyVar i)
specTypeToType tv (RFun {rt_in = fin, rt_out = fout}) = do
    t <- specTypeToType tv fin
    t2 <- specTypeToType tv fout
    
    case (t, t2) of
        (Just t', Just t2') -> return $ Just (TyFun t' t2')
        _ -> return Nothing
specTypeToType tv (RAllT {rt_tvbind = RTVar (RTV v) _, rt_ty = rty}) = do
    let i = mkIdUnsafe v
    t <- specTypeToType tv rty
    return $ fmap (TyForAll i) t
specTypeToType tv (RApp {rt_tycon = c, rt_args = as}) = rTyConType tv c as
specTypeToType tv (RAppTy {rt_arg = arg, rt_res = res}) = do
    argT <- specTypeToType tv arg
    resT <- specTypeToType tv res
    case (argT, resT) of
        (Just argT', Just resT') -> return $ Just (TyApp argT' resT')
        _ -> return Nothing
specTypeToType _ rty = error $ "Unmatched pattern in specTypeToType " ++ show (pprint rty)

rTyConType :: TV.TyVarEnv -> RTyCon -> [SpecType]-> LHStateM (Maybe Type)
rTyConType tv rtc sts = do
    tenv <- typeEnv

    let tcn = mkTyConNameUnsafe . rtc_tc $ rtc
        n = nameModMatch tcn tenv

    ts <- mapM (specTypeToType tv) sts
    
    case (not . any isNothing $ ts) of
        True -> case fmap (\n' -> mkFullAppedTyCon tv n' (catMaybes ts) TYPE) n of
                    Nothing -> return $ primType tcn
                    t -> return t
        False -> return Nothing

primType :: Name -> Maybe Type
primType (Name "Int#" _ _ _) = Just TyLitInt
primType (Name "Float#" _ _ _) = Just TyLitFloat
primType (Name "Double#" _ _ _) = Just TyLitDouble
primType (Name "Word#" _ _ _) = Just TyLitInt
primType _ = Nothing

sortToType :: Sort -> LHStateM Type
sortToType FInt = tyIntT
sortToType FReal = tyDoubleT
sortToType _ = error "Unhandled sort"

convertBrel :: Brel -> LHStateM Expr
convertBrel Ref.Eq = convertBrel' lhEqM
convertBrel Ref.Ueq = convertBrel' lhEqM
convertBrel Ref.Ne = convertBrel' lhNeM
convertBrel Ref.Gt = return . Var =<< lhGtE
convertBrel Ref.Ge = return . Var =<< lhGeE
convertBrel Ref.Lt = return . Var =<< lhLtE
convertBrel Ref.Le = return . Var =<<  lhLeE
convertBrel _ = error "convertBrel: Unhandled brel"

convertBrel' :: LHStateM Name -> LHStateM Expr
convertBrel' f = do
    n <- f

    a <- freshIdN TYPE
    lh <- lhTCM
    b <- tyBoolT
    let tva = TyVar a
        t = TyForAll 
                a
                (TyFun
                    (TyCon lh (TyFun TYPE TYPE))
                    (TyFun 
                        tva 
                        (TyFun tva b)
                    )
                )

    return $ Var $ Id n t

brelTCDict :: DictMaps -> Type -> LHStateM Expr
brelTCDict = lhTCDict

bopTCDict :: Bop -> DictMaps -> Type -> LHStateM Expr
bopTCDict Ref.Mod dm t = integralDict dm t
bopTCDict Ref.Div dm t = do
    fd <- maybeFractionalDict dm t
    case fd of
        Just fd' -> return fd'
        Nothing -> integralDict dm t
bopTCDict Ref.RDiv dm t =  do
    fd <- maybeFractionalDict dm t
    case fd of
        Just fd' -> return fd'
        Nothing -> integralDict dm t 
bopTCDict _ dm t = numDict dm t

lhTCDict :: DictMaps -> Type -> LHStateM Expr
lhTCDict m t = do
    lh <- lhTCM
    tc <- typeClassInstTC (lh_dicts m) lh t
    case tc of
        Just e -> return e
        Nothing -> error $ "No lh dict " ++ show lh ++ "\n" ++ show t ++ "\n" ++ show m

lhTCDict' :: LHDictMap -> Type -> LHStateM Expr
lhTCDict' m t = do
    lh <- lhTCM
    tc <- typeClassInstTC m lh t
    case tc of
        Just e -> return e
        Nothing -> error $ "No lh dict " ++ show lh ++ "\n" ++ show t ++ "\n" ++ show m

maybeOrdDict :: DictMaps -> Type -> LHStateM (Maybe Expr)
maybeOrdDict m t = do
    ordTC <- lhOrdTCM
    tc <- typeClassInstTC (ord_dicts m) ordTC t
    case tc of
        Just _ -> return tc
        Nothing -> do
            ord <- lhOrdM
            lh <- lhTCDict m t
            return . Just $ App (App (Var (Id ord TyUnknown)) (Type t)) lh


ordDict :: DictMaps -> Type -> LHStateM Expr
ordDict m t = do
    tc <- maybeOrdDict m t
    case tc of
        Just e -> return e
        Nothing -> error $ "No ord dict \n" ++ show t ++ "\n" ++ show m

maybeNumDict :: DictMaps -> Type -> LHStateM (Maybe Expr)
maybeNumDict m t = do
    num <- lhNumTCM
    typeClassInstTC (num_dicts m) num t

numDict :: DictMaps -> Type -> LHStateM Expr
numDict m t = do
    tc <- maybeNumDict m t
    case tc of
        Just e -> return e
        Nothing -> error $ "No num dict \n" ++ show t ++ "\n" ++ show m

maybeIntegralDict :: DictMaps -> Type -> LHStateM (Maybe Expr)
maybeIntegralDict m t = do
    integral <- return . KV.integralTC =<< knownValues
    typeClassInstTC (integral_dicts m) integral t

integralDict :: DictMaps -> Type -> LHStateM Expr
integralDict m t = do
    tc <- maybeIntegralDict m t
    case tc of
        Just e -> return e
        Nothing ->  error $ "No integral dict\n" ++ show t ++ "\n" ++ show m

maybeFractionalDict :: DictMaps -> Type -> LHStateM (Maybe Expr)
maybeFractionalDict m t = do
    integral <- return . KV.fractionalTC =<< knownValues
    typeClassInstTC (fractional_dicts m) integral t
