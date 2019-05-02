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
derivingG2Rep ty = do
    TyConI tycon <- reify ty

    let (tyConName, tyVars, cs) = case tycon of
            DataD _ nm tyvs _ css _ -> (nm, tyvs, css)
            NewtypeD _ nm tyvs _ c _ -> (nm, tyvs, [c])
            _ -> error "derivingG2Rep: Unsupported type"

    let instanceType = forallT [] (cxt $ map mkCxt tyVars)
                        $ conT ''G2Rep `appT` foldl apply (conT tyConName) tyVars

    sequence [instanceD (return []) instanceType [ genG2Rep tyConName tyVars cs
                                                 , genG2UnRep tyConName (length tyVars) cs
                                                 , genG2Type tyConName tyVars]]
    where
        apply t (PlainTV name)    = appT t (varT name)
        apply t (KindedTV name _) = appT t (varT name)

        mkCxt (PlainTV name) = conT ''G2Rep `appT` varT name
        mkCxt (KindedTV name _) = conT ''G2Rep `appT` varT name

genG2Rep :: TH.Name -> [TyVarBndr] -> [Con] -> Q Dec
genG2Rep tyConName tyVars cs = funD 'g2Rep (map (genG2RepClause tyConName tyVars) cs)

genG2RepClause :: TH.Name -> [TyVarBndr] -> Con -> Q Clause
genG2RepClause tyConName tyVars (NormalC name fieldTypes) =
    genG2RepClause' tyConName tyVars name fieldTypes
genG2RepClause tyConName tyVars (InfixC st1 n st2) =
    genG2RepClause' tyConName tyVars n [st1, st2]
genG2RepClause _ _ con = error $ "genG2RepClause: Unhandled case." ++ show con 

genG2RepClause' :: TH.Name -> [TyVarBndr] -> TH.Name -> [StrictType] -> Q Clause
genG2RepClause' tyConName tyVars dcNme fieldTypes = do
    tenv <- newName "tenv"
    cleaned <- newName "cleaned"
    fieldNames <- replicateM (length fieldTypes) (newName "x")

    let pats = varP tenv:varP cleaned:[conP dcNme (map varP fieldNames)]
        qqTyConName = thNameToQQName tyConName
        qqName = thNameToQQName dcNme

    let g2R = conE 'Data 
                `appE` (varE 'qqDataConLookupFallBack
                    `appE` litE (integerL $ toInteger $ length tyVars)
                    `appE` litE (integerL $ toInteger $ length fieldTypes)
                    `appE` qqNameToQExp qqTyConName
                    `appE` qqNameToQExp qqName
                    `appE` (varE 'qqMap `appE` varE cleaned `appE` varE tenv)
                    `appE` varE tenv)

        tys = map (\tyv -> conE 'Type
                            `appE` (varE 'g2Type
                                        `appE` varE tenv
                                        `appE` varE cleaned
                                        `appE` (sigE (varE 'undefined) (tyVBToType tyv)))
                  ) tyVars

        body = normalB $ appE (varE 'mkApp) $ listE
                    (g2R:tys ++ map (newField tenv cleaned) (zip fieldNames fieldTypes))

    clause pats body []
    where
        tyVBToType (PlainTV name) = varT name
        tyVBToType (KindedTV name _) = varT name

-- | Looks up a `DataCon` with the given type and data constructor name.
-- Falls back to creating a data constructor from scratch, if the data constructor
-- is not in the given TypeEnv.
-- We do this because the user of a QuasiQuoter may pass in types that are not
-- available when the QuasiQuoter is compiled 
qqDataConLookupFallBack :: Int -- The number of TyVars
                        -> Int -- The number of arguments
                        -> QQName -> QQName -> QQMap -> TypeEnv -> DataCon
qqDataConLookupFallBack tyv_n arg_n qqtn qqdc qqm tenv
    | Just dc <- qqDataConLookup qqtn qqdc qqm tenv = dc
    | otherwise =
        let
            n = G2.Name "unknown" Nothing 0 Nothing
            i = Id n TYPE

            ntb = NamedTyBndr i
            t = mkTyFun $ replicate (arg_n + 1) (TyCon n TYPE)
            t' = foldr TyForAll t (replicate tyv_n ntb)
        in
        DataCon (qqNameToName0 qqdc) t'

newField :: TH.Name -> TH.Name -> (TH.Name, StrictType) -> Q Exp
newField _ _ (x, (_, ConT n))
    | nameBase n == "Int#" = [|Lit . LitInt . toInteger $ $(conE 'I# `appE` varE x)|]
newField _ _ (x, (_, ConT n))
    | nameBase n == "Float#" = [|Lit . LitFloat . toRational $ $(conE 'F# `appE` varE x)|]
newField _ _ (x, (_, ConT n))
    | nameBase n == "Double#" = [|Lit . LitDouble . toRational $ $(conE 'D# `appE` varE x)|]
newField _ _ (x, (_, ConT n))
    | nameBase n == "Char#" = [|Lit . LitChar $ $(conE 'C# `appE` varE x)|]
newField tenv cleaned (x, _) = do
    return $ VarE 'g2Rep `AppE` VarE tenv `AppE` VarE cleaned `AppE` VarE x

genG2UnRep :: TH.Name -> Int -> [Con] -> Q Dec
genG2UnRep tyConName tyVarNum cs = funD 'g2UnRep (map (genG2UnRepClause tyConName tyVarNum) cs ++ [g2UnRepCatchAllClause])

genG2UnRepClause :: TH.Name -> Int -> Con -> Q Clause
genG2UnRepClause tyConName tyVarNum (NormalC name fieldTypes) =
    genG2UnRepClause' tyConName tyVarNum name fieldTypes
genG2UnRepClause tyConName tyVarNum (InfixC st1 n st2) =
    genG2UnRepClause' tyConName tyVarNum n [st1, st2]
genG2UnRepClause _ _ con = error $ "genG2RepClause: Unhandled case." ++ show con 

genG2UnRepClause' :: TH.Name -> Int -> TH.Name -> [StrictType] -> Q Clause
genG2UnRepClause' tyConName tyVarNum dcNme fieldTypes = do
    tenv <- newName "tenv"
    expr <- newName "expr"

    let pats = varP tenv:[varP expr]

    fieldNames <- replicateM (length fieldTypes) (newName "x")
    g2DCName <- newName "g2_dc"
    let guardPat1 = listP $ [p|Data (DataCon (G2.Name $(varP g2DCName) _ _ _) _)|]:replicate tyVarNum wildP ++ map varP fieldNames
        guardPat2 = [|T.unpack $(varE g2DCName) ==  $(litE . stringL $ nameBase dcNme) |]
    
    guardPat <- patG [bindS guardPat1 (varE 'unApp `appE` varE expr), noBindS guardPat2]
    ret <- appsE $ conE dcNme:map (newFieldUnRep tenv) (zip fieldNames fieldTypes)
    let guardRet = return (guardPat, ret)

    clause pats (guardedB [guardRet]) []

g2UnRepCatchAllClause :: Q Clause
g2UnRepCatchAllClause = do
    expr <- newName "expr"
    let pats = [wildP, varP expr]

    clause pats (normalB [|error $ "Unhandled case in g2UnRep" ++ show $(varE expr) |]) []

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

genG2Type :: TH.Name -> [TyVarBndr] -> Q Dec
genG2Type tyConName tyVars = funD 'g2Type [genG2TypeClause tyConName tyVars]

genG2TypeClause :: TH.Name -> [TyVarBndr] -> Q Clause
genG2TypeClause tyConName tyVars = do
    tenv <- newName "tenv"
    cleaned <- newName "cleaned"
    let pats = [varP tenv, varP cleaned, wildP]

    let qqTyConName = thNameToQQName tyConName
        exn = [|let
                    qqM = qqMap $(varE cleaned) $(varE tenv)
                    n = HM.lookup $(qqNameToQExp qqTyConName) qqM
               in
               case n of
                    Just n -> TyCon n TYPE
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
intPrimFromLit _ = error "intPrimFromLit: Unhandled Expr"

floatPrimFromLit :: G2.Expr -> Float#
floatPrimFromLit (Lit (LitFloat x)) =
    case fromRational x of
        F# x' -> x'
floatPrimFromLit _ = error "floatPrimFromLit: Unhandled Expr"

doublePrimFromLit :: G2.Expr -> Double#
doublePrimFromLit (Lit (LitDouble x)) =
    case fromRational x of
        D# x' -> x'
doublePrimFromLit _ = error "intPrimFromLit: Unhandled Expr"

charPrimFromLit :: G2.Expr -> Char#
charPrimFromLit (Lit (LitChar (C# x))) = x
charPrimFromLit _ = error "charPrimFromLit: Unhandled Expr"
