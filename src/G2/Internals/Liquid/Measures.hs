{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.Measures (Measures, createMeasures) where

import G2.Internals.Language
import qualified  G2.Internals.Language.ExprEnv as E
import G2.Internals.Liquid.Conversion
import G2.Internals.Liquid.TCValues
import G2.Internals.Liquid.Types
import Language.Haskell.Liquid.Types
import G2.Internals.Translation.Haskell

import qualified Data.Map as M
import Data.Maybe
import qualified GHC as GHC

import qualified Data.HashMap.Lazy as HM

-- Creates measures from LH measure specifications
-- We need this to support measures witten in comments
createMeasures :: [Measure SpecType GHC.DataCon] -> TCValues -> State h t -> (ExprEnv, NameGen)
createMeasures meas tcv s@(State {expr_env = eenv, type_env = tenv, name_gen = ng}) = 
    let
        nt = M.fromList $ mapMaybe (measureTypeMappings tenv tcv) meas

        meas' = mapMaybe (convertMeasure s tcv nt) $ filter (allTypesKnown tenv) meas

        eenvk = E.keys eenv
        mvNames = filter (flip notElem eenvk) $ varNames meas'

        eenv' = foldr (uncurry E.insert) eenv meas'
        (eenv'', ng') = doRenames mvNames ng eenv'
        -- (meas'', ng') = (meas', ng)
    in
    (eenv'', ng')

allTypesKnown :: TypeEnv -> Measure SpecType GHC.DataCon -> Bool
allTypesKnown tenv (M {sort = srt}) = isJust $ specTypeToType tenv srt

measureTypeMappings :: TypeEnv -> TCValues  -> Measure SpecType GHC.DataCon -> Maybe (Name, Type)
measureTypeMappings tenv tcv (M {name = n, sort = srt}) =
    let
        lh = lhTC tcv
        t = fmap (addLHDictToType lh) $ specTypeToType tenv srt
    in
    case t of
        Just t' -> Just (symbolName $ val n, t')
        _ -> Nothing

addLHDictToType :: Name -> Type -> Type
addLHDictToType lh t =
    let
        lhD = map (\i -> TyConApp lh [TyVar i]) $ tyForAllBindings t
    in
    foldr TyFun t lhD

convertMeasure :: State h t -> TCValues -> M.Map Name Type -> Measure SpecType GHC.DataCon -> Maybe (Name, Expr)
convertMeasure s@(State {type_env = tenv, name_gen = ng}) tcv m (M {name = n, sort = srt, eqns = eq}) =
    let
        -- nt = M.fromList $ convertSpecTypeDict tcv s srt

        n' = symbolName $ val n

        st = specTypeToType tenv srt
        
        bnds = tyForAllBindings $ fromJust st
        ds = map (Name "d" Nothing) [1 .. length bnds]
        nbnds = zip ds $ map TyVar bnds
        as = map (\(d, t) -> Id d $ TyConApp (lhTC tcv) [t]) nbnds
        as' = as ++ bnds

        as_t = map (\i -> (idName i, typeOf i)) as

        stArgs = nonTyForAllArgumentTypes $ fromJust st
        stRet = fmap returnType st

        (lam_i, ng1) = freshId (head stArgs) ng
        (cb, _) = freshId (head stArgs) ng1
        alts = mapMaybe (convertDefs s stArgs stRet tcv (M.union m (M.fromList as_t))) eq

        e = foldr Lam (Lam lam_i $ Case (Var lam_i) cb alts) as'
    in
    case st of -- [1]
        Just _ -> Just (n', e)
        Nothing -> Nothing

convertDefs :: State h t -> [Type] -> Maybe Type -> TCValues -> M.Map Name Type -> Def SpecType GHC.DataCon -> Maybe Alt
convertDefs s@(State {type_env = tenv}) [TyConApp _ st_t] ret tcv m (Def { ctor = dc, body = b, binds = bds}) =
    let
        (DataCon n t _) = mkData HM.empty HM.empty dc
        (TyConApp tn _) = returnType t
        dc' = getDataConNameMod tenv tn n
        
        -- See [1] below, we only evaluate this if Just
        dc''@(DataCon _ dct _) = fromJust dc'
        bnds = tyForAllBindings dct
        dctarg = nonTyForAllArgumentTypes dct

        -- Adjust the tyvars in the datacon to have the same ids as those we read from LH
        dctarg' = foldr (uncurry replaceASTs) dctarg $ zip (map TyVar bnds) st_t

        nt = map (\((sym, t'), t'') -> (symbolName sym, maybe t'' (unsafeSpecTypeToType tenv) t')) $ zip bds dctarg'

        is = map (uncurry Id) nt

        e = mkExprFromBody s ret tcv (M.union m $ M.fromList nt) b
    in
    case dc' of
        Just _ -> Just $ Alt (DataAlt dc'' is) e -- [1]
        Nothing -> Nothing

mkExprFromBody :: State h t -> Maybe Type -> TCValues  -> M.Map Name Type -> Body -> Expr
mkExprFromBody s ret tcv m (E e) = convertLHExpr e ret tcv s m
mkExprFromBody s ret tcv m (P e) = convertLHExpr e ret tcv s m