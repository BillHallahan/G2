{-# LANGUAGE TemplateHaskell #-}

module G2.Language.Internals.G2Rep ( G2Rep (..)
                                   , derivingG2Rep ) where

import G2.Language.Expr
import G2.Language.Support
import G2.Language.Syntax

import Control.Monad

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

    let instanceType = conT ''G2Rep `appT` foldl apply (conT tyConName) tyVars

    sequence [instanceD (return []) instanceType [genG2Rep tyConName cs]]
    where
        apply t (PlainTV name)    = appT t (varT name)
        apply t (KindedTV name _) = appT t (varT name)

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
        body = normalB $ appE (varE 'mkApp) $ listE $ 
                    undefined:map (newField tenv) (zip fieldNames fieldTypes)

    clause pats body []


newField :: TH.Name -> (TH.Name, StrictType) -> Q Exp
newField tenv (x, _) = return $ VarE 'g2Rep `AppE` VarE tenv `AppE` VarE x