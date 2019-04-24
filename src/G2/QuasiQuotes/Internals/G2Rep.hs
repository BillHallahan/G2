{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TemplateHaskell #-}

module G2.QuasiQuotes.Internals.G2Rep ( G2Rep (..)
                                      , derivingG2Rep ) where

import G2.Language.Expr
import G2.Language.Naming
import G2.Language.Support
import G2.Language.Syntax as G2
import G2.QuasiQuotes.Support

import Control.Monad

import qualified Data.Map as M
import qualified Data.Text as T

import GHC.Exts

import Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax as TH

import Debug.Trace

class G2Rep g where
    g2Rep :: TypeEnv -> CleanedNames -> g -> Expr
    g2UnRep :: TypeEnv -> CleanedNames -> Expr -> g

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

    sequence [instanceD (return []) instanceType [genG2Rep tyConName cs, genG2UnRep tyConName cs]]
    where
        apply t (PlainTV name)    = appT t (varT name)
        apply t (KindedTV name _) = appT t (varT name)

        mkCxt (PlainTV name) = conT ''G2Rep `appT` varT name
        mkCxt (KindedTV name _) = conT ''G2Rep `appT` varT name

genG2Rep :: TH.Name -> [Con] -> Q Dec
genG2Rep tyConName cs = funD 'g2Rep (map (genG2RepClause tyConName) cs)

genG2RepClause :: TH.Name -> Con -> Q Clause
genG2RepClause tyConName (NormalC name fieldTypes) =
    genG2RepClause' tyConName name fieldTypes
genG2RepClause tyConName (InfixC st1 n st2) =
    genG2RepClause' tyConName n [st1, st2]
genG2RepClause _ con = error $ "genG2RepClause: Unhandled case." ++ show con 

genG2RepClause' :: TH.Name -> TH.Name -> [StrictType] -> Q Clause
genG2RepClause' tyConName dcName fieldTypes = do
    tenv <- newName "tenv"
    cleaned <- newName "cleaned"
    fieldNames <- replicateM (length fieldTypes) (newName "x")

    let pats = varP tenv:varP cleaned:[conP dcName (map varP fieldNames)]
        qqTyConName = thNameToQQName tyConName
        qqName = thNameToQQName dcName

    runIO $ putStrLn $ "qqTyConName = " ++ show qqTyConName ++ "\nqqName = " ++ show qqName

    let g2R = conE 'Data 
                `appE` (varE 'qqDataConLookupFallBack
                    `appE` qqNameToQExp qqTyConName
                    `appE` qqNameToQExp qqName
                    `appE` (varE 'qqMap `appE` varE cleaned `appE` varE tenv)
                    `appE` varE tenv)

        body = normalB $ appE (varE 'mkApp) $ listE
                    (g2R:map (newField tenv cleaned) (zip fieldNames fieldTypes))

    clause pats body []

-- | Looks up a `DataCon` with the given type and data constructor name.
-- Falls back to creating a data constructor from scratch, if the data constructor
-- is not in the given TypeEnv.
-- We do this because the user of a QuasiQuoter may pass in types that are not
-- available when the QuasiQuoter is compiled 
qqDataConLookupFallBack :: QQName -> QQName -> QQMap -> TypeEnv -> DataCon
qqDataConLookupFallBack qqtn qqdc qqm tenv
    | Just dc <- qqDataConLookup qqtn qqdc qqm tenv = dc
    | otherwise = trace ("fallback on qqtn = " ++ show qqtn ++ "\nqqdc = " ++ show qqdc ++ "\nwith\n" ++ show (M.keys tenv)) DataCon (qqNameToName0 qqdc) TyUnknown

newField :: TH.Name -> TH.Name -> (TH.Name, StrictType) -> Q Exp
newField tenv _ (x, (_, ConT n))
    | nameBase n == "Int#" = [|Lit . LitInt . toInteger $ $(conE 'I# `appE` varE x)|]
newField tenv cleaned (x, _) = do
    return $ VarE 'g2Rep `AppE` VarE tenv `AppE` VarE cleaned `AppE` VarE x

genG2UnRep :: TH.Name -> [Con] -> Q Dec
genG2UnRep tyConName cs = funD 'g2UnRep (map (genG2UnRepClause tyConName) cs)

genG2UnRepClause :: TH.Name -> Con -> Q Clause
genG2UnRepClause tyConName (NormalC name fieldTypes) =
    genG2UnRepClause' tyConName name fieldTypes
genG2UnRepClause tyConName (InfixC st1 n st2) =
    genG2UnRepClause' tyConName n [st1, st2]
genG2UnRepClause _ con = error $ "genG2RepClause: Unhandled case." ++ show con 

genG2UnRepClause' :: TH.Name -> TH.Name -> [StrictType] -> Q Clause
genG2UnRepClause' tyConName dcName fieldTypes = do
    tenv <- newName "tenv"
    cleaned <- newName "cleaned"
    expr <- newName "expr"

    let pats = varP tenv:varP cleaned:[varP expr]
        qqTyConName = thNameToQQName tyConName
        qqDCName = thNameToQQName dcName

        unapped_expr = [| unApp $(varE expr) |]

    fieldNames <- replicateM (length fieldTypes) (newName "x")
    g2DCName <- newName "g2_dc"
    let guardPat1 = listP $ [p|Data (DataCon (G2.Name $(varP g2DCName) _ _ _) _)|]:map varP fieldNames
        guardPat2 = [|T.unpack $(varE g2DCName) ==  $(litE . stringL $ nameBase dcName) |]
    
    guardPat <- patG [bindS guardPat1 (varE 'unApp `appE` varE expr), noBindS guardPat2]
    ret <- appsE $ conE dcName:map (newFieldUnRep tenv cleaned) (zip fieldNames fieldTypes)
    let guardRet = return (guardPat, ret)

    clause pats (guardedB [guardRet]) []

newFieldUnRep :: TH.Name -> TH.Name -> (TH.Name, StrictType) -> Q Exp
newFieldUnRep tenv _ (x, (_, ConT n))
    | nameBase n == "Int#" = [| intPrimFromLit $(varE x) |]
newFieldUnRep tenv cleaned (x, _) = do
    varE 'g2UnRep `appE` varE tenv `appE` varE cleaned `appE` varE x

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