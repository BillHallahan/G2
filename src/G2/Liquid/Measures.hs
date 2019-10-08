{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.Measures (Measures, createMeasures) where

import G2.Language
import qualified  G2.Language.ExprEnv as E
import G2.Language.Monad
import G2.Liquid.Conversion
import G2.Liquid.Types
import Language.Haskell.Liquid.Types
import G2.Translation.Haskell

import Control.Monad.Extra

import qualified Data.Map as M
import Data.Maybe
import qualified GHC as GHC

import qualified Data.HashMap.Lazy as HM

-- | Creates measures from LH measure specifications.
-- This is required to find all measures that are written in comments.
createMeasures :: [Measure SpecType GHC.DataCon] -> LHStateM ()
createMeasures meas = do
    nt <- return . M.fromList =<< mapMaybeM measureTypeMappings meas
    meas' <- mapMaybeM (convertMeasure nt) =<< filterM allTypesKnown meas
    
    meenv <- measuresM
    let eenvk = E.keys meenv
        mvNames = filter (flip notElem eenvk) $ varNames meas'

    meenv' <- mapM (uncurry insertMeasureM) meas'
    _ <- doRenamesN mvNames meenv'

    return ()

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

    lam_i <- freshIdN (head stArgs)
    cb <- freshIdN (head stArgs)
    
    alts <- mapMaybeM (convertDefs stArgs stRet (M.fromList as_t) bt) eq

    let e = mkLams as' (Lam TermL lam_i $ Case (Var lam_i) cb alts) 
    
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
    , st_t <- tyAppArgs l_t = do
    tenv <- typeEnv
    let (DataCon n t) = mkData HM.empty HM.empty dc
        (TyCon tn _) = tyAppCenter $ returnType $ PresType t
        dc' = getDataConNameMod tenv tn n
        
        -- See [1] below, we only evaluate this if Just
        dc''@(DataCon _ dct) = fromJust dc'
        bnds = tyForAllBindings $ PresType dct
        dctarg = anonArgumentTypes $ PresType dct

        -- Adjust the tyvars in the datacon to have the same ids as those we read from LH
        dctarg' = foldr (uncurry replaceASTs) dctarg $ zip (map TyVar bnds) st_t

    nt <- mapM (\((sym, t'), t'') -> do
                    t''' <- maybeM (return t'') unsafeSpecTypeToType (return t')
                    return (symbolName sym, t''')) $ zip bds dctarg'

    let is = map (uncurry Id) nt

    e <- mkExprFromBody ret m (M.union bt $ M.fromList nt) b
    
    case dc' of
        Just _ -> return $ Just $ Alt (DataAlt dc'' is) e -- [1]
        Nothing -> return Nothing
convertDefs _ _ _ _ _ = error "convertDefs: Unhandled Type List"

mkExprFromBody :: Maybe Type -> LHDictMap -> BoundTypes -> Body -> LHStateM Expr
mkExprFromBody ret m bt (E e) = convertLHExpr (mkDictMaps m) bt ret e
mkExprFromBody ret m bt (P e) = convertLHExpr (mkDictMaps m) bt ret e
mkExprFromBody _ _ _ _ = error "mkExprFromBody: Unhandled Body"

mkDictMaps :: LHDictMap -> DictMaps
mkDictMaps ldm = DictMaps { lh_dicts = ldm
                          , num_dicts = M.empty
                          , integral_dicts = M.empty
                          , ord_dicts = M.empty}
