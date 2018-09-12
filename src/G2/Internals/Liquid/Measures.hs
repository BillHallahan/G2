{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Internals.Liquid.Measures (Measures, createMeasures) where

import G2.Internals.Language
import qualified  G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.Monad
import G2.Internals.Liquid.Conversion2
import G2.Internals.Liquid.TCValues
import G2.Internals.Liquid.Types
import Language.Haskell.Liquid.Types
import G2.Internals.Translation.Haskell

import Control.Monad.Extra

import qualified Data.Map as M
import Data.Maybe
import qualified GHC as GHC

import qualified Data.HashMap.Lazy as HM

import Debug.Trace

-- Creates measures from LH measure specifications
-- We need this to support measures written in comments
createMeasures :: [Measure SpecType GHC.DataCon] -> LHStateM ()
createMeasures meas = do
    nt <- return . M.fromList =<< mapMaybeM measureTypeMappings meas
    meas' <- mapMaybeM (convertMeasure nt) =<< filterM allTypesKnown meas
    
    meenv <- measuresM
    let eenvk = E.keys meenv
        mvNames = filter (flip notElem eenvk) $ varNames meas'

    meenv' <- mapM (uncurry insertMeasureM) meas'
    meenv'' <- doRenamesN mvNames meenv'

    return ()

allTypesKnown :: Measure SpecType GHC.DataCon -> LHStateM Bool
allTypesKnown (M {sort = srt}) = do
    st <- specTypeToType srt
    return $ isJust st

measureTypeMappings :: Measure SpecType GHC.DataCon -> LHStateM (Maybe (Name, Id))
measureTypeMappings (M {name = n, sort = srt}) = do
    st <- specTypeToType srt
    lh <- lhTCM

    let t = fmap (addLHDictToType lh) st

    let n' = symbolName $ val n
    
    case t of
        Just t' -> return $ Just (n', Id n' t')
        _ -> return  Nothing

addLHDictToType :: Name -> Type -> Type
addLHDictToType lh t =
    let
        lhD = map (\i -> mkTyConApp lh [TyVar i] TYPE) $ tyForAllBindings t
    in
    foldr TyFun t lhD

convertMeasure :: M.Map Name Id -> Measure SpecType GHC.DataCon -> LHStateM (Maybe (Name, Expr))
convertMeasure m (M {name = n, sort = srt, eqns = eq}) = do
    let n' = symbolName $ val n

    st <- specTypeToType srt
    lh_tc <- lhTCM
        
    let bnds = tyForAllBindings $ PresType $ fromJust st
        ds = map (\i -> Name "d" Nothing i Nothing) [1 .. length bnds]
        nbnds = zip ds $ map TyVar bnds
        as = map (\(d, t) -> Id d $ mkTyConApp lh_tc [t] TYPE) nbnds
        as' = map (TypeL, ) bnds ++ map (TermL,) as

        as_t = map (\i -> (idName i, i)) as

        stArgs = anonArgumentTypes . PresType $ fromJust st
        stRet = fmap returnType st

    lam_i <- freshIdN (head stArgs)
    cb <- freshIdN (head stArgs)
    
    alts <- mapMaybeM (convertDefs stArgs stRet (M.union m (M.fromList as_t))) eq

    let e = mkLams as' (Lam TermL lam_i $ Case (Var lam_i) cb alts) 
    
    case st of -- [1]
        Just _ -> return $ Just (n', e)
        Nothing -> return Nothing

convertDefs :: [Type] -> Maybe Type -> M.Map Name Id -> Def SpecType GHC.DataCon -> LHStateM (Maybe Alt)
convertDefs [l_t] ret m (Def { ctor = dc, body = b, binds = bds})
    | TyConApp _ _ <- tyAppCenter l_t
    , st_t <- tyAppArgs l_t = do
    tenv <- typeEnv
    let (DataCon n t) = mkData HM.empty HM.empty dc
        (TyConApp tn _) = tyAppCenter $ returnType $ PresType t
        dc' = getDataConNameMod tenv tn n
        
        -- See [1] below, we only evaluate this if Just
        dc''@(DataCon _ dct) = fromJust dc'
        bnds = tyForAllBindings dct
        dctarg = anonArgumentTypes dct

        -- Adjust the tyvars in the datacon to have the same ids as those we read from LH
        dctarg' = foldr (uncurry replaceASTs) dctarg $ zip (map TyVar bnds) st_t

    nt <- mapM (\((sym, t'), t'') -> do
                    t''' <- maybeM (return t'') unsafeSpecTypeToType (return t')
                    return (symbolName sym, Id (symbolName sym) t''')) $ zip bds dctarg'

    let is = map snd nt

    e <- mkExprFromBody ret (M.union m $ M.fromList nt) b
    
    case dc' of
        Just _ -> return $ Just $ Alt (DataAlt dc'' is) e -- [1]
        Nothing -> return Nothing
convertDefs _ _ _ _ = error "convertDefs: Unhandled Type List"

mkExprFromBody :: Maybe Type -> M.Map Name Id -> Body -> LHStateM Expr
mkExprFromBody ret m (E e) = convertLHExpr m ret e
mkExprFromBody ret m (P e) = convertLHExpr m ret e
mkExprFromBody _ _ _ = error "mkExprFromBody: Unhandled Body"