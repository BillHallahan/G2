{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.Naming
    ( NameGen
    , Renamable (rename)
    , doRename
    , doRenames
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

newtype NameGen = NameGen (HM.HashMap (String, Maybe String) Int)
                deriving (Show, Eq, Read)

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
                                    concatMap (\(Alt am _) -> altMatchNames am)
                                              as
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

doRename :: Renamable a => Name -> NameGen -> a -> (a, NameGen)
doRename n ngen x = (rename n n' x, ngen')
  where (n', ngen') = freshSeededName n ngen

doRenames :: Renamable a => [Name] -> NameGen -> a -> (a, NameGen)
doRenames [] ngen x = (x, ngen)
doRenames (n:ns) ngen x = doRenames ns ngen' x'
  where (x', ngen') = doRename n ngen x

-- |Renamable a
-- Given an old name and a new name, replaces the old name with the new name
-- everywhere in the passed type.
-- rename should be used only to define an instance.  Use rename to perform the
-- rename instead
class Renamable a where
    rename :: Name -> Name -> a -> a

instance Renamable Name where
    rename old new n = if old == n then new else n

instance Renamable Id where
    rename old new (Id n t) = Id (rename old new n) (rename old new t)

instance Renamable Expr where
    rename old new = modify go
      where
        go :: Expr -> Expr
        go (Var i) = Var (rename old new i)
        go (Data d) = Data (rename old new d)
        go (Lam i e) = Lam (rename old new i) e
        go (Let b e) =
            let b' = map (\(n, e') -> (rename old new n, e')) b
            in Let b' e
        go (Case e i a) =
            Case e (rename old new i) (rename old new a)
        go (Type t) = Type (rename old new t)
        go e = e

instance Renamable Type where
    rename old new = modify go
      where
        go :: Type -> Type
        go (TyVar n t) = TyVar (rename old new n) t
        go (TyConApp n ts) = TyConApp (rename old new n) ts
        go (TyForAll tb t) = TyForAll (rename old new tb) t
        go t = t

instance Renamable Alt where
    rename old new (Alt am e) = Alt (rename old new am) (rename old new e)

instance Renamable DataCon where
    rename old new (DataCon n t ts) =
        DataCon (rename old new n) (rename old new t) (rename old new ts)
    rename _ _ d = d

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
freshSeededName (Name n m _) (NameGen hm) = (Name n m i', NameGen hm')
  where i' = HM.lookupDefault 0 (n, m) hm
        hm' = HM.insert (n, m) (i' + 1) hm

freshSeededNames :: [Name] -> NameGen -> ([Name], NameGen)
freshSeededNames [] r = ([], r)
freshSeededNames (name:ns) r = (name':ns', ngen'') 
  where (name', ngen') = freshSeededName name r
        (ns', ngen'') = freshSeededNames ns ngen'

freshName :: NameGen -> (Name, NameGen)
freshName ngen = freshSeededName seed ngen
  where
    seed = Name "fs?" Nothing 0

freshNames :: Int -> NameGen -> ([Name], NameGen)
freshNames i ngen = freshSeededNames (replicate i (Name "fs?" Nothing 0)) ngen

