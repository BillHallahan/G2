module G2.Internals.Liquid.CreateMeasures where

import G2.Internals.Language
import G2.Internals.Liquid.Conversion
import G2.Internals.Liquid.TCValues
import G2.Internals.Translation.Haskell

import Language.Haskell.Liquid.Types

import qualified Data.Map as M
import Data.Maybe
import qualified GHC as GHC

import Debug.Trace

createMeasures :: [Measure SpecType GHC.DataCon] -> TCValues -> State -> [(Name, Expr)]
createMeasures meas tcv s@(State {type_env = tenv}) = 
	let
		nt = M.fromList $ mapMaybe (measureTypeMappings (type_env s)) meas

		meas' = mapMaybe (convertMeasure s tcv nt) $ filter (allTypesKnown tenv) meas
	in
	meas'

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
convertMeasure s@(State {expr_env = eenv, type_env = tenv, type_classes = tc, name_gen = ng}) tcv m (M {name = n, sort = srt, eqns = eq}) =
	let
		nt = M.fromList $ convertSpecTypeDict tcv s srt

		n' = symbolName $ val n

		st = specTypeToType tenv srt

		stArgs = nonTyForAllArgumentTypes $ fromJust st
		-- The fromJust in lhid is safe, because of the case st of at [1]
		-- We only access lhid in the Just case
		(lhid, ng1) = freshId (TyConApp (lhTC tcv) [fromJust st]) ng

		(lam_i, ng2) = freshId (head stArgs) ng1
		(cb, ng3) = freshId (head stArgs) ng2
		alts = mapMaybe (convertDefs s tcv (M.union m nt) lhid stArgs) eq
		
		e = Lam lam_i $ Case (Var lam_i) cb alts
	in
	case st of -- [1]
		Just _ -> Just (n', e)
		Nothing -> Nothing

convertDefs :: State -> TCValues -> M.Map Name Type -> LHId -> [Type] -> Def SpecType GHC.DataCon -> Maybe Alt
convertDefs s@(State {type_env = tenv}) tcv m lhid ts (Def { ctor = dc, dsort = srt, body = b, binds = bds}) =
	let
		dc'@(DataCon n t _) = mkData dc
		(TyConApp tn _) = returnType t
		dc'' = getDataConNameMod tenv n tn
		
		-- See [1] below, we only evaluate this if Just
		dc'''@(DataCon _ dct _) = fromJust dc''
		dctarg = nonTyForAllArgumentTypes dct

		nt = map (\((s, t), t')-> (symbolName s, maybe t' (unsafeSpecTypeToType tenv) t)) $ zip bds dctarg

		is = map (uncurry Id) nt

		e = mkExprFromBody s tcv (M.union m $ M.fromList nt) lhid b
	in
	case dc'' of
		Just _ -> Just $ Alt (DataAlt dc''' is) e -- [1]
		Nothing -> Nothing

mkExprFromBody :: State -> TCValues  -> M.Map Name Type-> LHId -> Body -> Expr
mkExprFromBody s tcv m lhid (E e) = convertLHExpr e tcv s m
mkExprFromBody s tcv m lhid (P e) = convertLHExpr e tcv s m