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

import Debug.Trace

-- Creates measures from LH measure specifications
-- We need this to support measures witten in comments
createMeasures :: [Measure SpecType GHC.DataCon] -> TCValues -> State -> State
createMeasures meas tcv s@(State {expr_env = eenv, type_env = tenv}) = 
    let
        nt = M.fromList $ mapMaybe (measureTypeMappings tenv) meas

        meas' = mapMaybe (convertMeasure s tcv nt) $ filter (allTypesKnown tenv) meas
    in
    s {expr_env = foldr (uncurry E.insert) eenv meas'}

type LHId = Id

allTypesKnown :: TypeEnv -> Measure SpecType GHC.DataCon -> Bool
allTypesKnown tenv (M {sort = srt}) = isJust $ specTypeToType tenv srt

measureTypeMappings :: TypeEnv -> Measure SpecType GHC.DataCon -> Maybe (Name, Type)
measureTypeMappings tenv (M {name = n, sort = srt}) =
    let
        t = specTypeToType tenv srt
    in
    case t of
        Just t' -> Just (symbolName $ val n, t')
        _ -> Nothing

convertMeasure :: State -> TCValues -> M.Map Name Type -> Measure SpecType GHC.DataCon -> Maybe (Name, Expr)
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

        -- The fromJust in lhid is safe, because of the case st of at [1]
        -- We only access lhid in the Just case
        (lhid, ng1) = freshId (TyConApp (lhTC tcv) [fromJust st]) ng

        (lam_i, ng2) = freshId (head stArgs) ng1
        (cb, ng3) = freshId (head stArgs) ng2
        alts = mapMaybe (convertDefs s tcv (M.union (M.union m nt) (M.fromList nbnds)) lhid bnds) eq

        e = foldr Lam (Lam lam_i $ Case (Var lam_i) cb alts) as'
    in
    case st of -- [1]
        Just _ -> Just (n', e)
        Nothing -> Nothing

convertDefs :: State -> TCValues -> M.Map Name Type -> LHId -> [Id] -> Def SpecType GHC.DataCon -> Maybe Alt
convertDefs s@(State {type_env = tenv}) tcv m lhid bnds (Def { ctor = dc, dsort = srt, body = b, binds = bds}) =
    let
        dc'@(DataCon n t _) = mkData dc
        (TyConApp tn _) = returnType t
        dc'' = getDataConNameMod tenv tn n
        
        -- See [1] below, we only evaluate this if Just
        dc'''@(DataCon _ dct _) = fromJust dc''
        bnds' = tyForAllBindings dct
        dctarg = nonTyForAllArgumentTypes dct

        -- Adjust the tyvars in the datacon to have the same ids as those we read from LH
        dctarg' = foldr (uncurry replaceASTs) dctarg $ zip (map TyVar bnds') (map TyVar bnds)

        nt = map (\((s, t), t')-> (symbolName s, maybe t' (unsafeSpecTypeToType tenv) t)) $ zip bds dctarg'

        is = map (uncurry Id) nt

        e = mkExprFromBody s tcv (M.union m $ M.fromList nt) lhid b
    in
    case dc'' of
        Just _ -> Just $ Alt (DataAlt dc''' is) e -- [1]
        Nothing -> Nothing

-- We remove the LH typeclass
-- This prevents there being two LH typeclasses, when it is added again in Conversion
-- removeLH :: Name -> Expr -> Expr
-- removeLH lh = modify (removeLH' lh)

-- removeLH' :: Name -> Expr -> Expr
-- removeLH' lh l@(Lam i e) = if tyConAppName (typeOf i) == Just lh then e else l
-- removeLH' lh a@(App e e') = if tyConAppName (typeOf e') == Just lh then e else a
-- removeLH' _ e = e

-- tyConAppName :: Type -> Maybe Name
-- tyConAppName (TyConApp n _) = Just n
-- tyConAppName _ = Nothing

mkExprFromBody :: State -> TCValues  -> M.Map Name Type-> LHId -> Body -> Expr
mkExprFromBody s tcv m lhid (E e) = convertLHExpr e tcv s m
mkExprFromBody s tcv m lhid (P e) = convertLHExpr e tcv s m