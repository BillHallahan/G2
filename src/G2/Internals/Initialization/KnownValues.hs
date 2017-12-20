module G2.Internals.Initialization.KnownValues (initKnownValues) where

import G2.Internals.Language.KnownValues
import G2.Internals.Language.Syntax
import G2.Internals.Language.TypeEnv

import qualified Data.Map as M

initKnownValues :: TypeEnv -> KnownValues
initKnownValues tenv =
	KnownValues {
		  tyInt = typeWithStrName tenv "Int"
		, tyFloat = typeWithStrName tenv "Float"
		, tyDouble = typeWithStrName tenv "Double"
		, tyBool = typeWithStrName tenv "Bool"

		, dcTrue = dcWithStrName tenv "Bool" "True"
		, dcFalse = dcWithStrName tenv "Bool" "False"
		}

typeWithStrName :: TypeEnv -> String -> Name
typeWithStrName tenv s =
	case M.toList $ M.filterWithKey (\(Name n _ _) _ -> n == s) tenv of
		(n, _):_ -> n
		_ -> error $ "No type found in typeWithStrName" ++ show s

dcWithStrName :: TypeEnv -> String -> String -> Name
dcWithStrName tenv ts dcs =
	case concatMap dataCon . M.elems $ M.filterWithKey (\(Name n _ _) _ -> n == ts) tenv of
		[] -> error "No type found in typeWithStrName"
		dc -> dcWithStrName' dc dcs

dcWithStrName' :: [DataCon] -> String -> Name
dcWithStrName' (DataCon n@(Name n' _ _) _ _:xs) s =
	if n' == s then n else dcWithStrName' xs s
dcWithStrName' (_:xs) s = dcWithStrName' xs s
dcWithStrName' _ _ = error "Np dc found in dcWithStrName"