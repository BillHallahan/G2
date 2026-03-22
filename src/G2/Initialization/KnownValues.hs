{-# LANGUAGE CPP, OverloadedStrings #-}

module G2.Initialization.KnownValues ( initKnownValues
                                     , addSmtStringFunc
                                     , recalcSmtStringFuncs ) where

import G2.Language.AST
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues
import G2.Language.Syntax
import G2.Language.TypeClasses
import G2.Language.TypeEnv
import G2.Language.Typing (tyAppCenter, returnType)

import Data.List
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import Data.Monoid
import qualified Data.Text as T

initKnownValues :: E.ExprEnv -> TypeEnv -> TypeClasses -> KnownValues
initKnownValues eenv tenv tc =
  let
    numT = typeWithStrName tenv "Num"
    integralT = typeWithStrName tenv "Integral"
    realT = typeWithStrName tenv "Real"
    eqT = typeWithStrName tenv "Eq"
    ordT = typeWithStrName tenv "Ord"

    type_index = exprWithStrName eenv "typeIndex#"
  in
  KnownValues {
      tyCoercion = typeWithStrName tenv "~#" 
    , dcCoercion = dcWithStrName tenv "~#" "Co"
    
    , tyInt = typeWithStrNameInModule tenv "Int" (Just "GHC.Types")
    , dcInt = dcWithStrNameInModule tenv "Int" "I#" (Just "GHC.Types")
    , tyFloat = typeWithStrNameInModule tenv "Float" (Just "GHC.Types")
    , dcFloat = dcWithStrNameInModule tenv "Float" "F#" (Just "GHC.Types")

    , tyDouble = typeWithStrNameInModule tenv "Double" (Just "GHC.Types")
    , dcDouble = dcWithStrNameInModule tenv "Double" "D#" (Just "GHC.Types")

    , tyInteger = typeWithStrName tenv "Integer"
    , dcInteger = dcWithStrName tenv "Integer" "Z#"

    , tyChar = typeWithStrNameInModule tenv "Char" (Just "GHC.Types")
    , dcChar = dcWithStrNameInModule tenv "Char" "C#" (Just "GHC.Types")

    , tyBool = typeWithStrNameInModule tenv "Bool" (Just "GHC.Types")
    , dcTrue = dcWithStrNameInModule tenv "Bool" "True" (Just "GHC.Types")
    , dcFalse = dcWithStrNameInModule tenv "Bool" "False" (Just "GHC.Types")

    , tyRational = typeWithStrName tenv "Rational"

#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
    , tyList = typeWithStrNameInModule tenv "List" (Just "GHC.Types")
    , dcCons = dcWithStrNameInModule tenv "List" ":" (Just "GHC.Types")
    , dcEmpty = dcWithStrNameInModule tenv "List" "[]" (Just "GHC.Types")
#else
    , tyList = typeWithStrNameInModule tenv "[]" (Just "GHC.Types")
    , dcCons = dcWithStrNameInModule tenv "[]" ":" (Just "GHC.Types")
    , dcEmpty = dcWithStrNameInModule tenv "[]" "[]" (Just "GHC.Types")
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

    , tyIP = typeWithStrName tenv "IP"

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

    , typeIndex = type_index
    , adjStr = exprWithStrName eenv "adjStr"
    , checkStrLazy = exprWithStrName eenv "checkStrLazy"

    , errorFunc = exprWithStrName eenv "error"
    , errorEmptyListFunc = exprWithStrName eenv "errorEmptyList"
    , errorWithoutStackTraceFunc = exprWithStrName eenv "errorWithoutStackTrace"
    , patErrorFunc = exprWithStrName eenv "patError"

    , smtStringFuncs = HS.empty
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

typeWithStrNameInModule :: TypeEnv -> T.Text -> Maybe T.Text -> Name
typeWithStrNameInModule tenv s s_mod =
  case HM.toList $ HM.filterWithKey (\(Name n mmod _ _) _ -> n == s && mmod == s_mod) tenv of
    (n, _):_ -> n
    _ -> error $ "No type found in typeWithStrName " ++ (show $ T.unpack s)

dcWithStrNameInModule :: TypeEnv -> T.Text -> T.Text -> Maybe T.Text -> Name
dcWithStrNameInModule tenv ts dcs s_mod =
  case concatMap dataCon . HM.elems $ HM.filterWithKey (\(Name n mmod _ _) _ -> n == ts && mmod == s_mod) tenv of
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
                t_c = tyAppCenter $ returnType t
            in
            case t_c of
                TyCon n _ -> n == sc_n
                _ -> False

addSmtStringFunc :: Name -> KnownValues -> KnownValues
addSmtStringFunc n kv = kv { smtStringFuncs = HS.insert n (smtStringFuncs kv) }

recalcSmtStringFuncs :: E.ExprEnv -> KnownValues -> KnownValues
recalcSmtStringFuncs eenv kv = kv { smtStringFuncs = mkSmtStringFuncs (typeIndex kv) eenv }

mkSmtStringFuncs :: Name -> E.ExprEnv -> HS.HashSet Name
mkSmtStringFuncs ty_ind = HS.fromList . E.keys . E.filter (getAny . evalASTs go)
  where
    go (Var (Id n _)) | n == ty_ind = Any True
    go _ = Any False