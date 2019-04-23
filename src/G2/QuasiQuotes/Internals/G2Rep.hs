{-# LANGUAGE TemplateHaskell #-}

module G2.QuasiQuotes.Internals.G2Rep ( G2Rep (..)
                                      , derivingG2Rep ) where

import G2.Language.Expr
import G2.Language.Support
import G2.Language.Syntax
import G2.QuasiQuotes.Support

import Control.Monad

import qualified Data.Text as T

import Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax as TH

class G2Rep g where
    g2Rep :: TypeEnv -> g -> Expr

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

    sequence [instanceD (return []) instanceType [genG2Rep tyConName cs]]
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
genG2RepClause' tyConName name fieldTypes = do
    tenv <- newName "tenv"
    fieldNames <- replicateM (length fieldTypes) (newName "x")

    let pats = varP tenv:[conP name (map varP fieldNames)]
        -- body = normalB $ appsE $ conE name:map (newField tenv) (zip fieldNames fieldTypes)

        -- g2R = qqDataConLookup (nameToQQName tyConName) (nameToQQName n) (qqMap tenv) --varE 'g2Rep `appE` varE tenv
        qqTyConName = thNameToQQName tyConName
        qqName = thNameToQQName name

    runIO $ putStrLn $ "qqTyConName = " ++ show qqTyConName ++ "\nqqName = " ++ show qqName

    let g2R = conE 'Data 
                `appE` (varE 'qqDataConLookupFallBack
                    `appE` qqNameToQExp qqTyConName
                    `appE` qqNameToQExp qqName
                    `appE` (varE 'qqMap `appE` varE tenv)
                    `appE` varE tenv)

        body = normalB $ appE (varE 'mkApp) $ listE
                    (g2R:map (newField tenv) (zip fieldNames fieldTypes))

    clause pats body []

-- | Looks up a `DataCon` with the given type and data constructor name.
-- Falls back to creating a data constructor from scratch, if the data constructor
-- is not in the given TypeEnv.
-- We do this because the user of a QuasiQuoter may pass in types that are not
-- available when the QuasiQuoter is compiled 
qqDataConLookupFallBack :: QQName -> QQName -> QQMap -> TypeEnv -> DataCon
qqDataConLookupFallBack qqtn qqdc qqm tenv
    | Just dc <- qqDataConLookup qqtn qqdc qqm tenv = dc
    | otherwise = DataCon (qqNameToName0 qqdc) undefined

newField :: TH.Name -> (TH.Name, StrictType) -> Q Exp
newField tenv (x, _) = return $ VarE 'g2Rep `AppE` VarE tenv `AppE` VarE x

qqNameToQExp :: QQName -> Q Exp
qqNameToQExp (QQName n Nothing) =
    conE 'QQName `appE` textToQExp n `appE` conE 'Nothing
qqNameToQExp (QQName n (Just m)) =
    conE 'QQName `appE` textToQExp n `appE` (conE 'Just `appE` textToQExp m)

textToQExp :: T.Text -> Q Exp
textToQExp t = varE 'T.pack `appE` litE (stringL (T.unpack t))