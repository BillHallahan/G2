{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.Naming
    ( NameGen
    , Renamable (renaming)
    , rename
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

rename :: Renamable a => Name -> NameGen -> a -> (a, NameGen)
rename n ng x =
    let
        (new, ng') = freshSeededName n ng
    in
    (renaming n new x, ng')

-- |Renamable a
-- Given an old name and a new name, replaces the old name with the new name
-- everywhere in the passed type.
-- renaming should be used only to define an instance.  Use rename to perform the
-- renaming instead
class Renamable a where
    renaming :: Name -> Name -> a -> a

instance Renamable Name where
    renaming old new n = if old == n then new else n

instance Renamable Id where
    renaming old new (Id n t) = Id (renaming old new n) (renaming old new t)

instance Renamable Expr where
    renaming old new = modify renaming'
        where
            renaming' :: Expr -> Expr
            renaming' (Var i) = Var (renaming old new i)
            renaming' (Data d) = Data (renaming old new d)
            renaming' (Lam i e) = Lam (renaming old new i) e
            renaming' (Let n e) = Let (renaming old new n) e
            renaming' (Case e i a) =
                Case e (renaming old new i) (renaming old new a)
            renaming' (Type t) = Type (renaming old new t)
            renaming' e = e

instance Renamable Type where
    renaming old new = modify renaming'
        where
            renaming' :: Type -> Type
            renaming' (TyVar n t) = TyVar (renaming old new n) t
            renaming' (TyConApp n ts) = TyConApp (renaming old new n) ts
            renaming' (TyForAll tb t) = TyForAll (renaming old new tb) t
            renaming' t = t

instance Renamable Alt where
    renaming old new (Alt am e) = Alt (renaming old new am) (renaming old new e)

instance Renamable DataCon where
    renaming old new (DataCon n t ts) =
        DataCon (renaming old new n) (renaming old new t) (renaming old new ts)
    renaming _ _ d = d

instance Renamable AltMatch where
    renaming old new (DataAlt dc i) =
        DataAlt (renaming old new dc) (renaming old new i)
    renaming _ _ am = am

instance Renamable TyBinder where
    renaming old new (NamedTyBndr n) = NamedTyBndr (renaming old new n)
    renaming _ _ tb = tb

instance (Functor f, Renamable a) => Renamable (f a) where
    renaming old new = fmap (renaming old new)

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