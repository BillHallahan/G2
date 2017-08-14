module G2.Internals.Language.Naming
    ( Renamer
    , nameToStr
    , renamer
    , freshName
    , freshNames
    , freshSeededName
    , freshSeededNames
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Syntax

import qualified Data.HashMap.Lazy as HM
import Data.List

newtype Renamer = Renamer (HM.HashMap (String, Maybe String) Int) deriving (Show, Eq, Read)

nameToStr :: Name -> String
nameToStr = undefined

renamer :: Program -> Renamer
renamer = Renamer
        . foldr (\(Name n m i) hm -> HM.insertWith (max) (n, m) i hm) HM.empty
        . allNames

allNames :: Program -> [Name]
allNames prog = nub (binds ++ expr_names ++ type_names)
  where
        binds = concatMap (map (idName . fst)) prog
        expr_names = evalASTs exprTopNames prog
        type_names = evalASTs typeTopNames prog

        exprTopNames :: Expr -> [Name]
        exprTopNames (Var var) = [idName var]
        exprTopNames (Lam b _) = [idName b]
        exprTopNames (Let kvs _) = map (idName . fst) kvs
        exprTopNames (Case _ cvar as) = idName cvar :
                                        concatMap (\(Alt am _) -> altMatchNames am) as
        exprTopNames _ = []

        altMatchNames :: AltMatch -> [Name]
        altMatchNames (DataAlt dc i) = dataConName dc ++ (map idName i)
        altMatchNames _ = []

        dataConName :: DataCon -> [Name]
        dataConName (DataCon n _ _) = [n]
        dataConName _ = []

        typeTopNames :: Type -> [Name]
        typeTopNames (TyVar n _) = [n]
        typeTopNames (TyConApp n _) = [n]
        typeTopNames (TyForAll (NamedTyBndr n) _) = [n]
        typeTopNames _ = []

freshSeededName :: Name -> Renamer -> (Name, Renamer)
freshSeededName (Name n m _) (Renamer hm) =
    let
        i' = HM.lookupDefault 0 (n, m) hm
        hm' = HM.insert (n, m) (i' + 1) hm
    in
    (Name n m i', Renamer hm')

freshSeededNames :: [Name] -> Renamer -> ([Name], Renamer)
freshSeededNames [] r = ([], r)
freshSeededNames (name:ns) r =
    let
        (name', confs') = freshSeededName name r
        (ns', confs'') = freshSeededNames ns confs'
    in
    (name':ns', confs'') 

freshName :: Renamer -> (Name, Renamer)
freshName confs = freshSeededName seed confs
  where
    seed = Name "fs?" Nothing 0

freshNames :: Int -> Renamer -> ([Name], Renamer)
freshNames i confs = freshSeededNames (replicate i (Name "fs?" Nothing 0)) confs