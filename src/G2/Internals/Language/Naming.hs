{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.Naming
    ( nameOccStr
    , NameGen
    , Named (names, rename)
    , doRename
    , doRenames
    , renameAll
    , nameToStr
    , strToName
    , mkNameGen
    , exprNames
    , typeNames
    , freshName
    , freshNames
    , freshSeededName
    , freshSeededNames
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Syntax

import qualified Data.HashMap.Lazy as HM
import Data.List
import Data.List.Utils

nameOccStr :: Name -> String
nameOccStr (Name occ _ _) = occ

newtype NameGen = NameGen (HM.HashMap (String, Maybe String) Int)
                deriving (Show, Eq, Read)

-- This relies on NameCleaner eliminating all '_', to preserve uniqueness
nameToStr :: Name -> String
nameToStr (Name n (Just m) i) = n ++ "_m_" ++ m ++ "_" ++ show i
nameToStr (Name n Nothing i) = n ++ "_n__" ++ show i

-- Inverse of nameToStr
strToName :: String -> Name
strToName str =
    let
        (n, _:q:_:mi) = breakList (\s -> isPrefixOf "_m_" s || isPrefixOf "_n_" s) str
        (m, _:i) = break ((==) '_') mi
        m' = if q == 'm' then Just m else Nothing
    in
    Name n m' (read i :: Int)

mkNameGen :: Program -> [ProgramType] -> NameGen
mkNameGen prog progTypes =
    NameGen
    . foldr (\(Name n m i) hm -> HM.insertWith (max) (n, m) (i + 1) hm) HM.empty
    $ names prog ++ names progTypes

exprNames :: (ASTContainer m Expr) => m -> [Name]
exprNames = evalASTs exprTopNames

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

typeNames :: (ASTContainer m Type) => m -> [Name]
typeNames = evalASTs typeTopNames

typeTopNames :: Type -> [Name]
typeTopNames (TyVar n _) = [n]
typeTopNames (TyConApp n _) = [n]
typeTopNames (TyForAll (NamedTyBndr v) _) = [idName v]
typeTopNames _ = []

doRename :: Named a => Name -> NameGen -> a -> (a, NameGen)
doRename n ngen x = (rename n n' x, ngen')
  where (n', ngen') = freshSeededName n ngen

doRenames :: Named a => [Name] -> NameGen -> a -> (a, NameGen)
doRenames [] ngen x = (x, ngen)
doRenames (n:ns) ngen x = doRenames ns ngen' x'
  where (x', ngen') = doRename n ngen x

renameAll :: (Named a) => a -> NameGen -> (a, NameGen)
renameAll x ng =
    let
        old = nub $ names x
    in
    doRenames old ng x

-- | Named a
-- Given an old name and a new name, replaces the old name with the new name
-- everywhere in the passed type.
-- rename should be used only to define an instance.  Use rename to perform the
-- rename instead
class Named a where
    names :: a -> [Name]
    rename :: Name -> Name -> a -> a

instance Named Name where
    names n = [n]
    rename old new n = if old == n then new else n

instance Named Id where
    names (Id n t) = n:names t
    rename old new (Id n t) = Id (rename old new n) (rename old new t)

instance Named Expr where
    names = eval go
        where
            go :: Expr -> [Name]
            go (Var i) = names i
            go (Prim _ t) = names t
            go (Data d) = names d
            go (Lam i _) = names i
            go (Let b _) = concatMap (names . fst) b
            go (Case _ i a) = names i ++ concatMap (names . altMatch) a
            go (Type t) = names t
            go _ = []

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
            Case e (rename old new i) (map goAlt a)
        go (Type t) = Type (rename old new t)
        go e = e
        
        goAlt :: Alt -> Alt
        goAlt (Alt am e) = Alt (rename old new am) e

instance Named Type where
    names = eval go
        where
            go (TyVar n _) = [n]
            go (TyConApp n _) = [n]
            go (TyForAll b _) = names b
            go _ = []

    rename old new = modify go
      where
        go :: Type -> Type
        go (TyVar n t) = TyVar (rename old new n) t
        go (TyConApp n ts) = TyConApp (rename old new n) ts
        go (TyForAll tb t) = TyForAll (rename old new tb) t
        go t = t

instance Named Alt where
    names (Alt am e) = names am ++ names e

    rename old new (Alt am e) = Alt (rename old new am) (rename old new e)

instance Named DataCon where
    names (DataCon n t ts) = n:(names t ++ concatMap names ts)
    names _ = []

    rename old new (DataCon n t ts) =
        DataCon (rename old new n) (rename old new t) (rename old new ts)
    rename _ _ d = d

instance Named AltMatch where
    names (DataAlt dc i) = names dc ++ names i
    names _ = []

    rename old new (DataAlt dc i) =
        DataAlt (rename old new dc) (rename old new i)
    rename _ _ am = am

instance Named TyBinder where
    names (NamedTyBndr i) = names i
    names _ = []

    rename old new (NamedTyBndr n) = NamedTyBndr (rename old new n)
    rename _ _ tb = tb

instance (Foldable f, Functor f, Named a) => Named (f a) where
    names = foldMap names
    rename old new = fmap (rename old new)

instance {-# OVERLAPPING #-} (Named a, Named b) => Named (a, b) where
    names (a, b) = names a ++ names b

    rename old new (a, b) = (rename old new a, rename old new b)

instance {-# OVERLAPPING #-} (Named a, Named b, Named c) => Named (a, b, c) where
    names (a, b, c) = names a ++ names b ++ names c

    rename old new (a, b, c) = (rename old new a, rename old new b, rename old new c)

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
