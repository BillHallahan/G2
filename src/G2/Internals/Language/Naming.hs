{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

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

    , freshSeededString
    , freshSeededStrings

    , freshName
    , freshNames
    , freshSeededName
    , freshSeededNames

    , freshId
    , freshSeededId
    , freshIds
    , freshVar

    ,childrenNames

    , mapNG
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.KnownValues
import G2.Internals.Language.Syntax
import G2.Internals.Language.TypeEnv

import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import Data.List.Utils

nameOccStr :: Name -> String
nameOccStr (Name occ _ _) = occ

data NameGen = NameGen { max_uniq :: (HM.HashMap (String, Maybe String) Int)
                       , dc_children :: (HM.HashMap Name [Name]) }
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
    let
        allNames = names prog ++ names progTypes
    in
    NameGen {
          max_uniq = 
            (foldr (\(Name n m i) hm -> HM.insertWith (max) (n, m) (i + 1) hm) 
                HM.empty allNames
            )
        , dc_children = HM.empty
    }

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
typeTopNames (TyVar i) = [idName i]
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
    name :: a -> Name
    names :: a -> [Name]
    rename :: Name -> Name -> a -> a

    name = head . names

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
            go (Cast _ c) = names c
            go (Coercion c) = names c
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
        go (Cast e c) = Cast e (rename old new c)
        go (Coercion c) = Coercion (rename old new c)
        go e = e

        goAlt :: Alt -> Alt
        goAlt (Alt am e) = Alt (rename old new am) e

instance Named Type where
    names = eval go
        where
            go (TyVar i) = names i
            go (TyConApp n _) = [n]
            go (TyForAll b _) = names b
            go _ = []

    rename old new = modify go
      where
        go :: Type -> Type
        go (TyVar i) = TyVar (rename old new i)
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

instance Named Coercion where
    names (t1 :~ t2) = names t1 ++ names t2

    rename old new (t1 :~ t2) = rename old new t1 :~ rename old new t2

instance Named AlgDataTy where
    names (DataTyCon ns dc) = ns ++ names dc
    names (NewTyCon ns dc rt) = ns ++ names dc ++ names rt

    rename old new (DataTyCon n dc) = DataTyCon (rename old new n) (rename old new dc)
    rename old new (NewTyCon n dc rt) = NewTyCon (rename old new n) (rename old new dc) (rename old new rt)

instance Named KnownValues where
    names (KnownValues {
              tyInt = tI
            , tyFloat = tF
            , tyDouble = tD

            , tyBool = tB
            , dcTrue = dcT
            , dcFalse = dcF
            }) =
            [tI, tF, tD, tB, dcT, dcF]

    rename old new (KnownValues {
                     tyInt = tI
                   , tyFloat = tF
                   , tyDouble = tD

                   , tyBool = tB
                   , dcTrue = dcT
                   , dcFalse = dcF
                   }) =
                    (KnownValues {
                          tyInt = rename old new tI
                        , tyFloat = rename old new tF
                        , tyDouble = rename old new tD

                        , tyBool = rename old new tB
                        , dcTrue = rename old new dcT
                        , dcFalse = rename old new dcF
                        })

instance (Foldable f, Functor f, Named a) => Named (f a) where
    names = foldMap names
    rename old new = fmap (rename old new)

instance {-# OVERLAPPING #-}  (Named s, Hashable s, Eq s) => Named (HS.HashSet s) where
    names = names . HS.toList 

    rename old new = HS.map (rename old new)

instance {-# OVERLAPPING #-} (Named a, Named b) => Named (a, b) where
    names (a, b) = names a ++ names b

    rename old new (a, b) = (rename old new a, rename old new b)

instance {-# OVERLAPPING #-} (Named a, Named b, Named c) => Named (a, b, c) where
    names (a, b, c) = names a ++ names b ++ names c

    rename old new (a, b, c) = (rename old new a, rename old new b, rename old new c)

freshSeededString :: String -> NameGen -> (Name, NameGen)
freshSeededString s = freshSeededName (Name s Nothing 0)

freshSeededStrings :: [String] -> NameGen -> ([Name], NameGen)
freshSeededStrings s = freshSeededNames (map (\s' -> Name s' Nothing 0) s)

freshSeededName :: Name -> NameGen -> (Name, NameGen)
freshSeededName (Name n m _) (NameGen { max_uniq = hm, dc_children = chm }) =
    (Name n m i', NameGen hm' chm)
    where 
        i' = HM.lookupDefault 0 (n, m) hm
        hm' = HM.insert (n, m) (i' + 1) hm

freshSeededNames :: [Name] -> NameGen -> ([Name], NameGen)
freshSeededNames [] r = ([], r)
freshSeededNames (n:ns) r = (n':ns', ngen'') 
  where (n', ngen') = freshSeededName n r
        (ns', ngen'') = freshSeededNames ns ngen'

freshName :: NameGen -> (Name, NameGen)
freshName ngen = freshSeededName seed ngen
  where
    seed = Name "fs?" Nothing 0

freshNames :: Int -> NameGen -> ([Name], NameGen)
freshNames i ngen = freshSeededNames (replicate i (Name "fs?" Nothing 0)) ngen

freshId :: Type -> NameGen -> (Id, NameGen)
freshId = freshSeededId (Name "fs?" Nothing 0)
    
freshSeededId :: Named a => a -> Type -> NameGen -> (Id, NameGen)
freshSeededId x t ngen =
    let
        (n, ngen') = freshSeededName (name x) ngen
    in
    (Id n t, ngen')

freshIds :: [Type] -> NameGen -> ([Id], NameGen)
freshIds ts ngen = 
    let
        (ns, ngen') = freshNames (length ts) ngen
    in
    (map (uncurry Id) (zip ns ts), ngen')

freshVar :: Type -> NameGen -> (Expr, NameGen)
freshVar t ngen =
    let
        (i, ngen') = freshId t ngen
    in
    (Var i, ngen')

-- Given the name n of a datacon, and some names for it's children,
-- returns new names ns for the children
-- Returns a new NameGen that will always return the same ns for that n
childrenNames :: Name -> [Name] -> NameGen -> ([Name], NameGen)
childrenNames n ns ng@(NameGen { dc_children = chm }) =
    let
        ens = HM.lookup n chm

        (fns, NameGen hm' chm') = freshSeededNames ns ng
        chm'' = HM.insert n fns chm'
    in
    case ens of
        Just ns' -> (ns', ng)
        Nothing -> (fns, NameGen hm' chm'')

-- Allows mapping, while passing a NameGen along
mapNG :: (a -> NameGen -> (b, NameGen)) -> [a] -> NameGen -> ([b], NameGen)
mapNG f xs ng = mapNG' f (reverse xs) ng []

mapNG' :: (a -> NameGen -> (b, NameGen)) -> [a] -> NameGen -> [b] -> ([b], NameGen)
mapNG' _ [] ng xs = (xs, ng)
mapNG' f (x:xs) ng xs' =
    let
        (x', ng') = f x ng
    in
    mapNG' f xs ng' (x':xs')
