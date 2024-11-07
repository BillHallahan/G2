{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.QuasiQuotes.Internals.G2Rep ( G2Rep (..)
                                      , derivingG2Rep
                                      , derivingG2RepTuples
                                      , derivingG2RepTuple ) where

import G2.Language.Expr
import G2.Language.Support
import G2.Language.Syntax as G2
import G2.QuasiQuotes.Support
import G2.Language.Typing

import Control.Monad

import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T

import GHC.Exts

import Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax as TH

class G2Rep g where
    g2Rep :: TypeEnv -> CleanedNames -> g -> Expr
    g2UnRep :: TypeEnv -> Expr -> g
    g2Type :: TypeEnv -> CleanedNames -> g -> G2.Type

-- Modeled after https://wiki.haskell.org/A_practical_Template_Haskell_Tutorial
derivingG2Rep :: TH.Name -> Q [Dec]
derivingG2Rep n = do
    stv <- isExtEnabled ScopedTypeVariables
    case stv of
        True -> return ()
        False -> error "derivingG2Rep: derivingG2Rep requires the language ScopedTypeVariables to be enabled"
    derivingG2Rep' n

derivingG2Rep' :: TH.Name -> Q [Dec]
derivingG2Rep' ty = do
    TyConI tycon <- reify ty

    let (tyConName, tvs, cs) = case tycon of
            DataD _ nm tyvs _ css _ -> (nm, tyvs, css)
            NewtypeD _ nm tyvs _ c _ -> (nm, tyvs, [c])
            _ -> error "derivingG2Rep: Unsupported type"

    let instanceType = forallT [] (cxt $ map mkCxt tvs)
                        $ conT ''G2Rep `appT` foldl apply (conT tyConName) tvs

    sequence [instanceD (return []) instanceType [ genG2Rep tyConName tvs cs
                                                 , genG2UnRep (length tvs) cs
                                                 , genG2Type tyConName]]
    where
#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
        apply t (PlainTV name _)    = appT t (varT name)
        apply t (KindedTV name _ _) = appT t (varT name)

        mkCxt (PlainTV name _) = conT ''G2Rep `appT` varT name
        mkCxt (KindedTV name _ _) = conT ''G2Rep `appT` varT name
#else
        apply t (PlainTV name)    = appT t (varT name)
        apply t (KindedTV name _) = appT t (varT name)

        mkCxt (PlainTV name) = conT ''G2Rep `appT` varT name
        mkCxt (KindedTV name _) = conT ''G2Rep `appT` varT name
#endif

#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
genG2Rep :: TH.Name -> [TyVarBndr ()] -> [Con] -> Q Dec
#else
genG2Rep :: TH.Name -> [TyVarBndr] -> [Con] -> Q Dec
#endif
genG2Rep tyConName tvs cs = funD 'g2Rep (map (genG2RepClause tyConName tvs) cs)

#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
genG2RepClause :: TH.Name -> [TyVarBndr ()] -> Con -> Q Clause
#else
genG2RepClause :: TH.Name -> [TyVarBndr] -> Con -> Q Clause
#endif
genG2RepClause tyConName tvs (NormalC name fieldTypes) =
    genG2RepClause' tyConName tvs name fieldTypes
genG2RepClause tyConName tvs (InfixC st1 n st2) =
    genG2RepClause' tyConName tvs n [st1, st2]
genG2RepClause _ _ con = error $ "genG2RepClause: Unhandled case." ++ show con 

#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
genG2RepClause' :: TH.Name -> [TyVarBndr ()] -> TH.Name -> [StrictType] -> Q Clause
#else
genG2RepClause' :: TH.Name -> [TyVarBndr] -> TH.Name -> [StrictType] -> Q Clause
#endif
genG2RepClause' tyConName tvs dcNme fieldTypes = do
    tenv <- newName "tenv_rep"
    cleaned <- newName "cleaned"
    fieldNames <- replicateM (length fieldTypes) (newName "x")

    let pats = varP tenv:varP cleaned:[conP dcNme (map varP fieldNames)]
        qqTyConName = thNameToQQName tyConName
        qqName = thNameToQQName dcNme

    let g2R = conE 'Data 
                `appE` (varE 'qqDataConLookupFallBack
                    `appE` litE (integerL $ toInteger $ length tvs)
                    `appE` litE (integerL $ toInteger $ length fieldTypes)
                    `appE` qqNameToQExp qqTyConName
                    `appE` qqNameToQExp qqName
                    `appE` (varE 'qqMap `appE` varE cleaned `appE` [|HM.keys $(varE tenv)|])
                    `appE` (varE 'qqMap `appE` varE cleaned `appE` [|map dcName . concatMap dataCon . HM.elems $ $(varE tenv)|])
                    `appE` varE tenv)

        tys = map (\tyv -> conE 'Type
                            `appE` (varE 'g2Type
                                        `appE` varE tenv
                                        `appE` varE cleaned
                                        `appE` (sigE (varE 'undefined) (tyVBToType tyv)))
                  ) tvs

        body = normalB $ appE (varE 'mkApp) $ listE
                    (g2R:tys ++ map (newField tenv cleaned) (zip fieldNames fieldTypes))

    clause pats body []
    where
#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
        tyVBToType (PlainTV name _) = varT name
        tyVBToType (KindedTV name _ _) = varT name
#else
        tyVBToType (PlainTV name) = varT name
        tyVBToType (KindedTV name _) = varT name
#endif

-- | Looks up a `DataCon` with the given type and data constructor name.
-- Falls back to creating a data constructor from scratch, if the data constructor
-- is not in the given TypeEnv.
-- We do this because the user of a QuasiQuoter may pass in types that are not
-- available when the QuasiQuoter is compiled 
qqDataConLookupFallBack :: Int -- The number of TyVars
                        -> Int -- The number of arguments
                        -> QQName -> QQName -> QQMap -> QQMap -> TypeEnv -> DataCon
qqDataConLookupFallBack tyv_n arg_n qqtn qqdc type_nm_qqm dc_nm_qqm tenv
    | Just dc <- qqDataConLookup qqtn qqdc type_nm_qqm dc_nm_qqm tenv = dc
    | otherwise =
        let
            n = G2.Name "unknown" Nothing 0 Nothing
            i = Id n TYPE

            t = mkTyFun $ replicate (arg_n + 1) (TyCon n TYPE)
            ty_forall_ids = replicate tyv_n i
            t' = foldr TyForAll t ty_forall_ids
        in
        DataCon (qqNameToName0 qqdc) t' ty_forall_ids []

newField :: TH.Name -> TH.Name -> (TH.Name, StrictType) -> Q Exp
newField _ _ (x, (_, ConT n))
    | nameBase n == "Int#" = [|Lit . LitInt . toInteger $ $(conE 'I# `appE` varE x)|]
newField _ _ (x, (_, ConT n))
    | nameBase n == "Float#" = [|Lit . LitFloat $ $(conE 'F# `appE` varE x)|]
newField _ _ (x, (_, ConT n))
    | nameBase n == "Double#" = [|Lit . LitDouble $ $(conE 'D# `appE` varE x)|]
newField _ _ (x, (_, ConT n))
    | nameBase n == "Char#" = [|Lit . LitChar $ $(conE 'C# `appE` varE x)|]
newField tenv cleaned (x, _) = do
    return $ VarE 'g2Rep `AppE` VarE tenv `AppE` VarE cleaned `AppE` VarE x

genG2UnRep :: Int -> [Con] -> Q Dec
genG2UnRep tyVarNum cs = funD 'g2UnRep (map (genG2UnRepClause tyVarNum) cs ++ [g2UnRepCatchAllClause])

genG2UnRepClause :: Int -> Con -> Q Clause
genG2UnRepClause tyVarNum (NormalC name fieldTypes) =
    genG2UnRepClause' tyVarNum name fieldTypes
genG2UnRepClause tyVarNum (InfixC st1 n st2) =
    genG2UnRepClause' tyVarNum n [st1, st2]
genG2UnRepClause _ con = error $ "genG2RepClause: Unhandled case." ++ show con 

genG2UnRepClause' :: Int -> TH.Name -> [StrictType] -> Q Clause
genG2UnRepClause' tyVarNum dcNme fieldTypes = do
    expr <- newName "expr"

    fieldNames <- replicateM (length fieldTypes) (newName "x")
    g2DCName <- newName "g2_dc"
    let guardPat1 = listP $ [p|Data (DataCon (G2.Name $(varP g2DCName) _ _ _) _ _ _)|]:replicate tyVarNum wildP ++ map varP fieldNames
        guardPat2 = [|T.unpack $(varE g2DCName) ==  $(litE . stringL $ nameBase dcNme) |]
    
    guardPat <- patG [bindS guardPat1 (varE 'unApp `appE` varE expr), noBindS guardPat2]

    case zip fieldNames fieldTypes of
        [] -> do
            let pats = wildP:[varP expr]

            ret <- conE dcNme
            let guardRet = return (guardPat, ret)

            clause pats (guardedB [guardRet]) []
        fnt@(fnt_h:_) -> do
            tenv <- newName "tenv_unrep"
            let pats = if usesTEnvUnRep (snd fnt_h) then varP tenv:[varP expr] else wildP:[varP expr]

            ret <- appsE $ conE dcNme:map (newFieldUnRep tenv) fnt
            let guardRet = return (guardPat, ret)

            clause pats (guardedB [guardRet]) []

g2UnRepCatchAllClause :: Q Clause
g2UnRepCatchAllClause = do
    expr <- newName "expr"
    let pats = [wildP, varP expr]

    clause pats (normalB [|error $ "Unhandled case in g2UnRep " ++ show $(varE expr) |]) []

newFieldUnRep :: TH.Name -> (TH.Name, StrictType) -> Q Exp
newFieldUnRep _ (x, (_, ConT n))
    | nameBase n == "Int#" = [| intPrimFromLit $(varE x) |]
newFieldUnRep _ (x, (_, ConT n))
    | nameBase n == "Float#" = [| floatPrimFromLit $(varE x) |]
newFieldUnRep _ (x, (_, ConT n))
    | nameBase n == "Double#" = [| doublePrimFromLit $(varE x) |]
newFieldUnRep _ (x, (_, ConT n))
    | nameBase n == "Char#" = [| charPrimFromLit $(varE x) |]
newFieldUnRep tenv (x, _) = do
    varE 'g2UnRep `appE` varE tenv `appE` varE x

usesTEnvUnRep :: StrictType -> Bool
usesTEnvUnRep (_, ConT n) =
    let nb = nameBase n in
    not (nb == "Int#" || nb == "Float#" || nb == "Double#" || nb == "Char#")
usesTEnvUnRep _ = True

genG2Type :: TH.Name -> Q Dec
genG2Type tyConName = funD 'g2Type [genG2TypeClause tyConName]

genG2TypeClause :: TH.Name -> Q Clause
genG2TypeClause tyConName = do
    tenv <- newName "tenv_type"
    cleaned <- newName "cleaned"
    let pats = [varP tenv, varP cleaned, wildP]

    let qqTyConName = thNameToQQName tyConName
        exn = [|let
                    qqM = qqMap $(varE cleaned) $(varE tenv)
                    n = HM.lookup $(qqNameToQExp qqTyConName) qqM
               in
               case n of
                    Just tcn -> TyCon tcn TYPE
                    Nothing -> TyCon (G2.Name (T.pack "Unknown") Nothing 0 Nothing) TYPE|]

    clause pats (normalB exn) []

derivingG2RepTuples :: Int -> Int -> Q [Dec]
derivingG2RepTuples mi ma = return . concat =<< mapM derivingG2RepTuple [mi..ma]

derivingG2RepTuple :: Int -> Q [Dec]
derivingG2RepTuple n = derivingG2Rep (tupleTypeName n)

qqNameToQExp :: QQName -> Q Exp
qqNameToQExp (QQName n Nothing) =
    conE 'QQName `appE` textToQExp n `appE` conE 'Nothing
qqNameToQExp (QQName n (Just m)) =
    conE 'QQName `appE` textToQExp n `appE` (conE 'Just `appE` textToQExp m)

textToQExp :: T.Text -> Q Exp
textToQExp t = varE 'T.pack `appE` litE (stringL (T.unpack t))

intPrimFromLit :: G2.Expr -> Int#
intPrimFromLit (Lit (LitInt x)) =
    case fromInteger x of
        I# x' -> x'
intPrimFromLit e = error $ "intPrimFromLit: Unhandled Expr" ++ show e

floatPrimFromLit :: G2.Expr -> Float#
floatPrimFromLit (Lit (LitFloat (F# x))) = x
floatPrimFromLit _ = error "floatPrimFromLit: Unhandled Expr"

doublePrimFromLit :: G2.Expr -> Double#
doublePrimFromLit (Lit (LitDouble (D# x))) = x
doublePrimFromLit _ = error "intPrimFromLit: Unhandled Expr"

charPrimFromLit :: G2.Expr -> Char#
charPrimFromLit (Lit (LitChar (C# x))) = x
charPrimFromLit _ = error "charPrimFromLit: Unhandled Expr"
