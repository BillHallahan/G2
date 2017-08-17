{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.Naming
    ( NameGen
    , Renamable (rename)
    , nameToStr
    , mkNameGen
    , freshName
    , freshNames
    , freshSeededName
    , freshSeededNames
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Syntax

import qualified Data.HashMap.Lazy as HM
import Data.List

newtype NameGen = NameGen (HM.HashMap (String, Maybe String) Int) deriving (Show, Eq, Read)

nameToStr :: Name -> String
nameToStr (Name n (Just m) i) = n ++ "_j_m_" ++ m ++ "_" ++ show i
nameToStr (Name n Nothing i) = n ++ "_j_a_" ++ show i

mkNameGen :: Program -> NameGen
mkNameGen = NameGen
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

class Renamable a where
    rename :: Name -> Name -> a -> a

instance Renamable Name where
    rename old new n = if old == n then new else n

instance Renamable Id where
    rename old new (Id n t) = Id (rename old new n) (rename old new t)

instance Renamable Expr where
    rename old new = modify rename'
        where
            rename' :: Expr -> Expr
            rename' (Var i) = Var (rename old new i)
            rename' (Data d) = Data (rename old new d)
            rename' (Lam i e) = Lam (rename old new i) e
            rename' (Let n e) = Let (rename old new n) e
            rename' (Case e i a) =
                Case e (rename old new i) (rename old new a)
            rename' (Type t) = Type (rename old new t)
            rename' e = e

instance Renamable Type where
    rename old new = modify rename'
        where
            rename' :: Type -> Type
            rename' (TyVar n t) = TyVar (rename old new n) t
            rename' (TyConApp n ts) = TyConApp (rename old new n) ts
            rename' (TyForAll tb t) = TyForAll (rename old new tb) t
            rename' t = t

instance Renamable Alt where
    rename old new (Alt am e) = Alt (rename old new am) (rename old new e)

instance Renamable DataCon where
    rename old new (DataCon n t ts) =
        DataCon (rename old new n) (rename old new t) (rename old new ts)

instance Renamable AltMatch where
    rename old new (DataAlt dc i) =
        DataAlt (rename old new dc) (rename old new i)
    rename _ _ am = am

instance Renamable TyBinder where
    rename old new (NamedTyBndr n) = NamedTyBndr (rename old new n)
    rename _ _ tb = tb

instance (Functor f, Renamable a) => Renamable (f a) where
    rename old new = fmap (rename old new)

freshSeededName :: Name -> NameGen -> (Name, NameGen)
freshSeededName (Name n m _) (NameGen hm) =
    let
        i' = HM.lookupDefault 0 (n, m) hm
        hm' = HM.insert (n, m) (i' + 1) hm
    in
    (Name n m i', NameGen hm')

freshSeededNames :: [Name] -> NameGen -> ([Name], NameGen)
freshSeededNames [] r = ([], r)
freshSeededNames (name:ns) r =
    let
        (name', confs') = freshSeededName name r
        (ns', confs'') = freshSeededNames ns confs'
    in
    (name':ns', confs'') 

freshName :: NameGen -> (Name, NameGen)
freshName confs = freshSeededName seed confs
  where
    seed = Name "fs?" Nothing 0

freshNames :: Int -> NameGen -> ([Name], NameGen)
freshNames i confs = freshSeededNames (replicate i (Name "fs?" Nothing 0)) confs