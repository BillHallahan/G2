{-# LANGUAGE CPP, OverloadedStrings #-}

module G2.Initialization.KnownValues (initKnownValues) where

import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues
import G2.Language.Syntax
import G2.Language.TypeClasses
import G2.Language.TypeEnv
import G2.Language.Typing (PresType (..), tyAppCenter, returnType)

import Data.List
import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T

initKnownValues :: E.ExprEnv -> TypeEnv -> TypeClasses -> KnownValues
initKnownValues eenv tenv tc =
  let
    numT = typeWithStrName tenv "Num"
    integralT = typeWithStrName tenv "Integral"
    realT = typeWithStrName tenv "Real"
    eqT = typeWithStrName tenv "Eq"
    ordT = typeWithStrName tenv "Ord"
  in
  KnownValues {
      tyCoercion = typeWithStrName tenv "~#" 
    , dcCoercion = dcWithStrName tenv "~#" "Co"
    , tyInt = typeWithStrName tenv "Int"
    , dcInt = dcWithStrName tenv "Int" "I#"
    , tyFloat = typeWithStrName tenv "Float"
    , dcFloat = dcWithStrName tenv "Float" "F#"

    , tyDouble = typeWithStrName tenv "Double"
    , dcDouble = dcWithStrName tenv "Double" "D#"

    , tyInteger = typeWithStrName tenv "Integer"
    , dcInteger = dcWithStrName tenv "Integer" "Z#"

    , tyChar = typeWithStrName tenv "Char"
    , dcChar = dcWithStrName tenv "Char" "C#"

    , tyBool = typeWithStrName tenv "Bool"
    , dcTrue = dcWithStrName tenv "Bool" "True"
    , dcFalse = dcWithStrName tenv "Bool" "False"

    , tyRational = typeWithStrName tenv "Rational"

#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
    , tyList = typeWithStrName tenv "List"
    , dcCons = dcWithStrName tenv "List" ":"
    , dcEmpty = dcWithStrName tenv "List" "[]"
#else
    , tyList = typeWithStrName tenv "[]"
    , dcCons = dcWithStrName tenv "[]" ":"
    , dcEmpty = dcWithStrName tenv "[]" "[]"
#endif

    , tyMaybe = typeWithStrName tenv "Maybe"
    , dcJust = dcWithStrName tenv "Maybe" "Just"
    , dcNothing = dcWithStrName tenv "Maybe" "Nothing"

  
#if MIN_VERSION_GLASGOW_HASKELL(9,8,0,0)
    , tyUnit = typeWithStrName tenv "Unit"
    , dcUnit = dcWithStrName tenv "Unit" "()"
#else
    , tyUnit = typeWithStrName tenv "()"
    , dcUnit = dcWithStrName tenv "()" "()"
#endif

    , tyPrimTuple = typeWithStrName tenv "(#,#)"
    , dcPrimTuple = dcWithStrName tenv "(#,#)" "(#,#)"

    , tyMutVar = typeWithStrName tenv "MutVar#"
    , dcMutVar = dcWithStrName tenv "MutVar#" "MutVar#"
    , tyState = typeWithStrName tenv "State#"
    , dcState = dcWithStrName tenv "State#" "State#"
    , tyRealWorld = typeWithStrName tenv "RealWorld"
    , dcRealWorld = dcWithStrName tenv "RealWorld" "RealWorld"

    , tyHandle = typeWithStrName tenv "Handle"

    , eqTC = eqT
    , numTC = numT
    , ordTC = ordT
    , integralTC = integralT
    , realTC = realT
    , fractionalTC = typeWithStrName tenv "Fractional"

    , integralExtactReal = superClassExtractor tc integralT realT
    , realExtractNum = superClassExtractor tc realT numT
    , realExtractOrd = superClassExtractor tc realT ordT
    , ordExtractEq = superClassExtractor tc ordT eqT

    , eqFunc = exprWithStrName eenv "=="
    , neqFunc = exprWithStrName eenv "/="

    , plusFunc = exprWithStrName eenv "+"
    , minusFunc = exprWithStrName eenv "-"
    , timesFunc = exprWithStrName eenv "*"
    , divFunc = exprWithStrName eenv "/"
    , negateFunc = exprWithStrName eenv "negate"
    , modFunc = exprWithStrName eenv "mod"

    , fromIntegerFunc = exprWithStrName eenv "fromInteger"
    , toIntegerFunc = exprWithStrName eenv "toInteger"

    , toRatioFunc = exprWithStrName eenv "%"
    , fromRationalFunc = exprWithStrName eenv "fromRational"

    , geFunc = exprWithStrName eenv ">="
    , gtFunc = exprWithStrName eenv ">"
    , ltFunc = exprWithStrName eenv "<"
    , leFunc = exprWithStrName eenv "<="

    , impliesFunc = exprWithStrName eenv "implies"
    , iffFunc = exprWithStrName eenv "iff"

    , andFunc = exprWithStrName eenv "&&"
    , orFunc = exprWithStrName eenv "||"
    , notFunc = exprWithStrName eenv "not"

    , typeIndex = exprWithStrName eenv "typeIndex#"
    , adjStr = exprWithStrName eenv "adjStr"

    , errorFunc = exprWithStrName eenv "error"
    , errorEmptyListFunc = exprWithStrName eenv "errorEmptyList"
    , errorWithoutStackTraceFunc = exprWithStrName eenv "errorWithoutStackTrace"
    , patErrorFunc = exprWithStrName eenv "patError"
    }

exprWithStrName :: E.ExprEnv -> T.Text -> Name
exprWithStrName eenv s =
  case filter (\(Name n _ _ _) -> n == s) $ E.keys eenv of
    n:_ -> n
    _ -> error $ "No expr found in exprWithStrName " ++ (show $ T.unpack s)

typeWithStrName :: TypeEnv -> T.Text -> Name
typeWithStrName tenv s =
  case HM.toList $ HM.filterWithKey (\(Name n _ _ _) _ -> n == s) tenv of
    (n, _):_ -> n
    _ -> error $ "No type found in typeWithStrName " ++ (show $ T.unpack s)

dcWithStrName :: TypeEnv -> T.Text -> T.Text -> Name
dcWithStrName tenv ts dcs =
  case concatMap dataCon . HM.elems $ HM.filterWithKey (\(Name n _ _ _) _ -> n == ts) tenv of
    [] -> error $ "No type found in dcWithStrName [" ++
                  (show $ T.unpack ts) ++ "] [" ++ (show $ T.unpack dcs) ++ "]"
    dc -> dcWithStrName' dc dcs

dcWithStrName' :: [DataCon] -> T.Text -> Name
dcWithStrName' (DataCon n@(Name n' _ _ _) _ _ _:xs) s =
  if n' == s then n else dcWithStrName' xs s
dcWithStrName' _ s = error $ "No dc found in dcWithStrName [" ++ (show $ T.unpack s) ++ "]"

superClassExtractor :: TypeClasses -> Name -> Name -> Name
superClassExtractor tc tc_n sc_n =
    case lookupTCClass tc_n tc of
        Just c
            | Just (_, i) <- find extractsSC (superclasses c) -> idName i
            | otherwise -> error $ "superClassExtractor: Extractor not found\n" ++ show sc_n ++ "\n" ++ show (superclasses c)
        Nothing -> error $ "superClassExtractor: Class not found " ++ show tc_n
    where
        extractsSC (t, _) =
            let
                t_c = tyAppCenter . returnType . PresType $ t
            in
            case t_c of
                TyCon n _ -> n == sc_n
                _ -> False
