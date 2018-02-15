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

import Debug.Trace

-- Creates measures from LH measure specifications
-- We need this to support measures witten in comments
createMeasures :: [Measure SpecType GHC.DataCon] -> TCValues -> State t -> State t
createMeasures meas tcv s@(State {expr_env = eenv, type_env = tenv}) = 
    let
        nt = M.fromList $ mapMaybe (measureTypeMappings tenv tcv) meas

        meas' = mapMaybe (convertMeasure s tcv nt) $ filter (allTypesKnown tenv) meas
    in
    s {expr_env = foldr (uncurry E.insert) eenv meas'}

allTypesKnown :: TypeEnv -> Measure SpecType GHC.DataCon -> Bool
allTypesKnown tenv (M {sort = srt}) = isJust $ specTypeToType tenv srt

measureTypeMappings :: TypeEnv-> TCValues  -> Measure SpecType GHC.DataCon -> Maybe (Name, Type)
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

convertMeasure :: State t -> TCValues -> M.Map Name Type -> Measure SpecType GHC.DataCon -> Maybe (Name, Expr)
convertMeasure s@(State {type_env = tenv, name_gen = ng}) tcv m (M {name = n, sort = srt, eqns = eq}) =
    let
        nt = M.fromList $ convertSpecTypeDict tcv s srt

        n' = symbolName $ val n

        st = specTypeToType tenv srt
        
        bnds = tyForAllBindings $ fromJust st
        ds = map (Name "d" Nothing) [1 .. length bnds]
        nbnds = zip ds $ map TyVar bnds
        as = map (\(d, t) -> Id d $ TyConApp (lhTC tcv) [t]) nbnds
        as' = as ++ bnds

        stArgs = nonTyForAllArgumentTypes $ fromJust st

        (lam_i, ng1) = freshId (head stArgs) ng
        (cb, _) = freshId (head stArgs) ng1
        alts = fixAlts s tcv m $ mapMaybe (convertDefs s tcv (M.union (M.union m nt) (M.fromList nbnds)) bnds) eq

        e = foldr Lam (Lam lam_i $ Case (Var lam_i) cb alts) as'
    in
    case st of -- [1]
        Just _ -> Just (n', e)
        Nothing -> Nothing

convertDefs :: State t -> TCValues -> M.Map Name Type -> [Id] -> Def SpecType GHC.DataCon -> Maybe Alt
convertDefs s@(State {type_env = tenv}) tcv m bnds (Def { ctor = dc, body = b, binds = bds}) =
    let
        (DataCon n t _) = mkData HM.empty HM.empty dc
        (TyConApp tn _) = returnType t
        dc' = getDataConNameMod tenv tn n
        
        -- See [1] below, we only evaluate this if Just
        dc''@(DataCon _ dct _) = fromJust dc'
        bnds' = tyForAllBindings dct
        dctarg = nonTyForAllArgumentTypes dct

        -- Adjust the tyvars in the datacon to have the same ids as those we read from LH
        dctarg' = foldr (uncurry replaceASTs) dctarg $ zip (map TyVar bnds') (map TyVar bnds)

        nt = map (\((sym, t'), t'')-> (symbolName sym, maybe t'' (unsafeSpecTypeToType tenv) t')) $ zip bds dctarg'

        is = map (uncurry Id) nt

        e = mkExprFromBody s tcv (M.union m $ M.fromList nt) b
    in
    case dc' of
        Just _ -> Just $ Alt (DataAlt dc'' is) e -- [1]
        Nothing -> Nothing


mkExprFromBody :: State t -> TCValues  -> M.Map Name Type -> Body -> Expr
mkExprFromBody s tcv m (E e) = convertLHExpr e tcv s m
mkExprFromBody s tcv m (P e) = convertLHExpr e tcv s m

--Adjusts the alts, to make sure they all return the same Type
fixAlts :: State t -> TCValues -> M.Map Name Type -> [Alt] -> [Alt]
fixAlts s@(State {known_values = kv}) tcv m alts =
    let
        anyInt = any (\(Alt _ e) -> typeOf e == tyInt kv) alts
    in
    if anyInt then map (convertInteger s tcv m) alts else alts

convertInteger :: State t -> TCValues -> M.Map Name Type -> Alt -> Alt
convertInteger s@(State {expr_env = eenv, known_values = kv, type_classes = tc}) tcv m a@(Alt am e) =
    let
        fIntgr = mkFromInteger eenv
        t = tyInt kv
        lhdict = fromJustErr "No lhDict for callFromInteger" $ lhTCDict eenv tcv tc t m
        ndict = fromJustErr "No numDict for callFromInteger" $ numDict eenv kv tc t m

        e' = mkApp [fIntgr, lhdict, Type t, ndict, e]
        a' = Alt am e'
    in
    if typeOf e == tyInteger kv then a' else a

fromJustErr :: String -> Maybe a -> a
fromJustErr _ (Just x) = x
fromJustErr s _ = error s