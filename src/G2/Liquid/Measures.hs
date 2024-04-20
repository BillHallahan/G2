{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.Measures (Measures, createMeasures, filterMeasures', measureTypeMappings) where

import G2.Language
import qualified  G2.Language.ExprEnv as E
import G2.Language.Monad
import G2.Liquid.Conversion
import G2.Liquid.Types
import Language.Haskell.Liquid.Types
import G2.Translation.Haskell

import Control.Monad.Extra

import Data.List
import Data.Maybe
import qualified GHC as GHC

import qualified Data.HashMap.Lazy as HM

-- | Creates measures from LH measure specifications.
-- This is required to find all measures that are written in comments.
createMeasures :: [Measure SpecType GHC.DataCon] -> LHStateM ()
createMeasures meas = do
    nt <- return . HM.fromList =<< mapMaybeM measureTypeMappings meas
    meas' <- mapMaybeM (convertMeasure nt) =<< filterM allTypesKnown meas
    
    filterMeasures (HM.keys nt)

    meenv <- measuresM
    let eenvk = E.keys meenv
        mvNames = filter (flip notElem eenvk) $ varNames meas'

    meenv' <- mapM (uncurry insertMeasureM) meas'
    _ <- doRenamesN mvNames meenv'

    return ()

-- | We remove any names covered by the Measures found by LH from the Measures we already have
-- to prevent using the wrong measures later
filterMeasures :: [Name] -> LHStateM ()
filterMeasures nt = do
    pre_meenv <- measuresM
    fil_meenv <- filterMeasures' pre_meenv nt
    putMeasuresM fil_meenv

filterMeasures' :: Measures -> [Name] -> LHStateM Measures
filterMeasures' pre_meenv nt = do
    let ns = map (\(Name n m _ _) -> (n, m)) nt
        fil_meenv = E.filterWithKey (\(Name n m _ _) _ -> (n, m) `notElem` ns) pre_meenv
    return fil_meenv

allTypesKnown :: Measure SpecType GHC.DataCon -> LHStateM Bool
#if MIN_VERSION_liquidhaskell(0,8,6)
allTypesKnown (M {msSort = srt}) = do
#else
allTypesKnown (M {sort = srt}) = do
#endif
    st <- specTypeToType srt
    return $ isJust st

measureTypeMappings :: Measure SpecType GHC.DataCon -> LHStateM (Maybe (Name, Type))
#if MIN_VERSION_liquidhaskell(0,8,6)
measureTypeMappings (M {msName = n, msSort = srt}) = do
#else
measureTypeMappings (M {name = n, sort = srt}) = do
#endif
    st <- specTypeToType srt
    lh <- lhTCM

    let t = fmap (addLHDictToType lh) st

    let n' = symbolName $ val n
    
    case t of
        Just t' -> return $ Just (n', t')
        _ -> return  Nothing

addLHDictToType :: Name -> Type -> Type
addLHDictToType lh t =
    let
        lhD = map (\i -> mkFullAppedTyCon lh [TyVar i] TYPE) $ tyForAllBindings $ PresType t
    in
    mapInTyForAlls (\t' -> foldr TyFun t' lhD) t

convertMeasure :: BoundTypes -> Measure SpecType GHC.DataCon -> LHStateM (Maybe (Name, Expr))
#if MIN_VERSION_liquidhaskell(0,8,6)
convertMeasure bt (M {msName = n, msSort = srt, msEqns = eq}) = do
#else
convertMeasure bt (M {name = n, sort = srt, eqns = eq}) = do
#endif
    let n' = symbolName $ val n

    st <- specTypeToType srt
    lh_tc <- lhTCM
        
    let bnds = tyForAllBindings $ PresType $ fromJust st
        ds = map (\i -> Name "d" Nothing i Nothing) [1 .. length bnds]
        nbnds = zip ds $ map TyVar bnds
        as = map (\(d, t) -> Id d $ mkFullAppedTyCon lh_tc [t] TYPE) nbnds
        as' = map (TypeL, ) bnds ++ map (TermL,) as

        as_t = map (\i -> (forType $ typeOf i, i)) as

        stArgs = anonArgumentTypes . PresType $ fromJust st
        stRet = fmap (returnType . PresType) st

    lam_i <- mapM freshIdN stArgs
    cb <- freshIdN (head stArgs)
    
    alts <- mapMaybeM (convertDefs stArgs stRet (HM.fromList as_t) bt) eq
    fls <- mkFalseE
    let defTy = maybe TyUnknown (returnType . PresType) st
        defAlt = Alt Default $ Assume Nothing fls (Prim Undefined defTy)

    let e = mkLams (as' ++ map (TermL,) lam_i) $ Case (Var (head lam_i)) cb defTy (defAlt:alts) 
    
    case st of -- [1]
        Just _ -> return $ Just (n', e)
        Nothing -> return Nothing
    where
        forType :: Type -> Name
        forType (TyApp _ (TyVar (Id n' _))) = n'
        forType _ = error "Bad type in forType"

convertDefs :: [Type] -> Maybe Type -> LHDictMap -> BoundTypes -> Def SpecType GHC.DataCon -> LHStateM (Maybe Alt)
convertDefs [l_t] ret m bt (Def { ctor = dc, body = b, binds = bds})
    | TyCon _ _ <- tyAppCenter l_t
    , st_t <- tyAppArgs l_t
    , dc' <- mkDataUnsafe dc = do
    tenv <- typeEnv
    let         
        -- See [1] below, we only evaluate this if Just
        dc''@(DataCon _ dct) = fixNamesDC tenv dc'
        bnds = tyForAllBindings $ PresType dct
        dctarg = anonArgumentTypes $ PresType dct

        -- Adjust the tyvars in the datacon to have the same ids as those we read from LH
        dctarg' = foldr (uncurry replaceASTs) dctarg $ zip (map TyVar bnds) st_t

    nt <- mapM (\((sym, t'), t'') -> do
                    t''' <- maybeM (return t'') unsafeSpecTypeToType (return t')
                    return (symbolName sym, t''')) $ zip bds dctarg'

    let is = map (uncurry Id) nt

    e <- mkExprFromBody ret m (HM.union bt $ HM.fromList nt) b
    
    return $ Just $ Alt (DataAlt dc'' is) e -- [1]
    | otherwise = return Nothing
convertDefs _ _ _ _ _ = error "convertDefs: Unhandled Type List"

fixNamesDC :: TypeEnv -> DataCon -> DataCon
fixNamesDC tenv (DataCon n t) =
    let
        (TyCon tn _) = tyAppCenter $ returnType $ PresType t
    in
    case getDataConNameMod tenv tn n of
        Just (DataCon dcn _) -> DataCon dcn (fixNamesType tenv t)
        Nothing -> error "fixNamesDC: Bad DC"

fixNamesType :: TypeEnv -> Type -> Type
fixNamesType tenv = modify (fixNamesType' tenv)

fixNamesType' :: TypeEnv -> Type -> Type
fixNamesType' tenv (TyCon n k) =
    case getTypeNameMod tenv n of
        Just n' -> TyCon n' k
        Nothing -> error "fixNamesType: Bad Type"
fixNamesType' _ t = t

getTypeNameMod :: TypeEnv -> Name -> Maybe Name
getTypeNameMod tenv (Name n m _ _) = find (\(Name n' m' _ _) -> n == n' && m == m') $ HM.keys tenv

mkExprFromBody :: Maybe Type -> LHDictMap -> BoundTypes -> Body -> LHStateM Expr
mkExprFromBody ret m bt (E e) = convertLHExpr (mkDictMaps m) bt ret e
mkExprFromBody ret m bt (P e) = convertLHExpr (mkDictMaps m) bt ret e
mkExprFromBody ret m bt (R s e) = do
    let s_nm = symbolName s
        t = maybe (error "mkExprFromBody: ret type unknown") id ret
        i = Id s_nm t

        bt' = HM.insert s_nm t bt
    g2_e <- convertLHExpr (mkDictMaps m) bt' ret e
    return . Let [(i, SymGen SNoLog t)] . Assume Nothing g2_e $ Var i 

mkDictMaps :: LHDictMap -> DictMaps
mkDictMaps ldm = DictMaps { lh_dicts = ldm
                          , num_dicts = HM.empty
                          , integral_dicts = HM.empty
                          , fractional_dicts = HM.empty
                          , ord_dicts = HM.empty}
