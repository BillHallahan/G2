{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Initialization.KnownValues (initKnownValues) where

import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.KnownValues
import G2.Internals.Language.Syntax
import G2.Internals.Language.TypeEnv

import qualified Data.Map as M
import qualified Data.Text as T

initKnownValues :: E.ExprEnv -> TypeEnv -> KnownValues
initKnownValues eenv tenv =
  KnownValues {
      tyInt = typeWithStrName tenv "Int"
    , dcInt = dcWithStrName tenv "Int" "I#"

    , tyFloat = typeWithStrName tenv "Float"
    , dcFloat = dcWithStrName tenv "Float" "F#"

    , tyDouble = typeWithStrName tenv "Double"
    , dcDouble = dcWithStrName tenv "Double" "D#"

    , tyInteger = typeWithStrName tenv "Integer"
    , dcInteger = dcWithStrName tenv "Integer" "Z#"

    , tyBool = typeWithStrName tenv "Bool"
    , dcTrue = dcWithStrName tenv "Bool" "True"
    , dcFalse = dcWithStrName tenv "Bool" "False"

    , tyList = typeWithStrName tenv "[]"
    , dcCons = dcWithStrName tenv "[]" ":"
    , dcEmpty = dcWithStrName tenv "[]" "[]"

    , eqTC = typeWithStrName tenv "Eq"
    , numTC = typeWithStrName tenv "Num"
    , ordTC = typeWithStrName tenv "Ord"
    , integralTC = typeWithStrName tenv "Integral"

    , eqFunc = exprWithStrName eenv "=="
    , neqFunc = exprWithStrName eenv "/="
    , geFunc = exprWithStrName eenv ">="
    , gtFunc = exprWithStrName eenv ">"
    , ltFunc = exprWithStrName eenv "<"
    , leFunc = exprWithStrName eenv "<="

    , structEqTC = Name "NotDefinedYet" Nothing 0 Nothing
    , structEqFunc = Name "NotDefinedYet" Nothing 0 Nothing

    , andFunc = exprWithStrName eenv "&&"
    , orFunc = exprWithStrName eenv "||"

    , patErrorFunc = exprWithStrName eenv "patError"
    }

exprWithStrName :: E.ExprEnv -> T.Text -> Name
exprWithStrName eenv s =
  case E.toList $ E.filterWithKey (\(Name n _ _ _) _ -> n == s) eenv of
    (n, _):_ -> n
    _ -> error $ "No expr found in exprWithStrName " ++ (show $ T.unpack s)

typeWithStrName :: TypeEnv -> T.Text -> Name
typeWithStrName tenv s =
  case M.toList $ M.filterWithKey (\(Name n _ _ _) _ -> n == s) tenv of
    (n, _):_ -> n
    _ -> error $ "No type found in typeWithStrName " ++ (show $ T.unpack s)

dcWithStrName :: TypeEnv -> T.Text -> T.Text -> Name
dcWithStrName tenv ts dcs =
  case concatMap dataCon . M.elems $ M.filterWithKey (\(Name n _ _ _) _ -> n == ts) tenv of
    [] -> error $ "No type found in typeWithStrName [" ++
                  (show $ T.unpack ts) ++ "] [" ++ (show $ T.unpack dcs) ++ "]"
    dc -> dcWithStrName' dc dcs

dcWithStrName' :: [DataCon] -> T.Text -> Name
dcWithStrName' (DataCon n@(Name n' _ _ _) _ _:xs) s =
  if n' == s then n else dcWithStrName' xs s
dcWithStrName' _ s = error $ "No dc found in dcWithStrName [" ++ (show $ T.unpack s) ++ "]"

