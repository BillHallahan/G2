{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Language.Naming
    ( nameOccStr
    , NameGen
    , Named (names, rename, renames)
    , doRename
    , doRenames
    , renameAll
    , nameToStr
    , strToName
    , mkNameGen
    , exprNames
    , typeNames

    , renameExpr
    , renameVars

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

    , childrenNames

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
import qualified Data.Text as T

nameOccStr :: Name -> T.Text
nameOccStr (Name occ _ _) = occ

data NameGen = NameGen { max_uniq :: (HM.HashMap (T.Text, Maybe T.Text) Int)
                       , dc_children :: (HM.HashMap Name [Name]) }
                deriving (Show, Eq, Read)

-- This relies on NameCleaner eliminating all '_', to preserve uniqueness
nameToStr :: Name -> String
nameToStr (Name n (Just m) i) = T.unpack n ++ "_m_" ++ T.unpack m ++ "_" ++ show i
nameToStr (Name n Nothing i) = T.unpack n ++ "_n__" ++ show i

-- Inverse of nameToStr
strToName :: String -> Name
strToName str =
    let
        (n, _:q:_:mi) = breakList (\s -> isPrefixOf "_m_" s || isPrefixOf "_n_" s) str
        (m, _:i) = break ((==) '_') mi
        m' = if q == 'm' then Just m else Nothing
    in
    Name (T.pack n) (fmap T.pack m') (read i :: Int)

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
doRenames ns ng e =
    let
        (ns', ng') = freshSeededNames ns ng
        hm = HM.fromList $ zip ns ns'
    in
    (renames hm e, ng')

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
    renames :: HM.HashMap Name Name -> a -> a

    name = head . names
    renames hm e = HM.foldrWithKey (\k v -> rename k v) e hm

instance Named Name where
    names n = [n]
    rename old new n = if old == n then new else n
    renames hm n = HM.lookupDefault n n hm

instance Named Id where
    names (Id n t) = n:names t
    rename old new (Id n t) = Id (rename old new n) (rename old new t)
    renames hm (Id n t) = Id (renames hm n) (renames hm t)

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
            go (Assert is _ _) = names is
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
        go (Assert is e e') = Assert (rename old new is) e e'
        go e = e

        goAlt :: Alt -> Alt
        goAlt (Alt am e) = Alt (rename old new am) e

    renames hm = modify go
        where
            go :: Expr -> Expr
            go (Var i) = Var (renames hm i)
            go (Data d) = Data (renames hm d)
            go (Lam i e) = Lam (renames hm i) e
            go (Let b e) = 
                let b' = map (\(n, e') -> (renames hm n, e')) b
                in Let b' e
            go (Case e i a) = Case e (renames hm i) (map goAlt a)
            go (Type t) = Type (renames hm t)
            go (Cast e c) = Cast e (renames hm c)
            go (Coercion c) = Coercion (renames hm c)
            go (Assert is e e') = Assert (renames hm is) e e'
            go e = e

            goAlt :: Alt -> Alt
            goAlt (Alt am e) = Alt (renames hm am) e

-- Rename only the names in an Expr that are the Name of an Id/Let/Data/Case Binding.
-- Does not change Types.
renameExpr :: ASTContainer m Expr => Name -> Name -> m -> m
renameExpr old new = modifyASTs (renameExpr' old new)

renameExpr' :: Name -> Name -> Expr -> Expr
renameExpr' old new (Var i) = Var (renameExprId old new i)
renameExpr' old new (Data d) = Data (renameExprDataCon old new d)
renameExpr' old new (Lam i e) = Lam (renameExprId old new i) e
renameExpr' old new (Let b e) = Let (map (\(b', e') -> (renameExprId old new b', e')) b) e
renameExpr' old new (Case e i a) = Case e (renameExprId old new i) $ map (renameExprAlt old new) a
renameExpr' old new (Assert is e e') = Assert (fmap (renameAssertTrackExpr old new) is) e e'
renameExpr' _ _ e = e


renameVars :: ASTContainer m Expr => Name -> Name -> m -> m
renameVars old new = modifyASTs (renameVars' old new)

renameVars' :: Name -> Name -> Expr -> Expr
renameVars' old new (Var i) = Var (renameExprId old new i)
renameVars' old new (Lam i e) = Lam (renameExprId old new i) e
renameVars' old new (Let b e) = Let (map (\(b', e') -> (renameExprId old new b', e')) b) e
renameVars' old new (Case e i a) = Case e (renameExprId old new i) $ map (renameExprAltIds old new) a
renameVars' old new (Assert is e e') = Assert (fmap (renameAssertTrackExpr old new) is) e e'
renameVars' _ _ e = e


renameExprId :: Name -> Name -> Id -> Id
renameExprId old new (Id n t) = Id (rename old new n) t

renameExprDataCon :: Name -> Name -> DataCon -> DataCon
renameExprDataCon old new (DataCon n t ts) = DataCon (rename old new n) t ts

renameExprAlt :: Name -> Name -> Alt -> Alt
renameExprAlt old new (Alt (DataAlt dc is) e) =
    let
        dc' = renameExprDataCon old new dc
        is' = map (renameExprId old new) is
    in
    Alt (DataAlt dc' is') e
renameExprAlt _ _ a = a

renameExprAltIds :: Name -> Name -> Alt -> Alt
renameExprAltIds old new (Alt (DataAlt dc is) e) =
    let
        is' = map (renameExprId old new) is
    in
    Alt (DataAlt dc is') e
renameExprAltIds _ _ a = a

renameAssertTrackExpr :: Name -> Name -> (Name, [Id], Id) -> (Name, [Id], Id)
renameAssertTrackExpr old new (n, is, i) = (rename old new n, map (renameExprId old new) is, renameExprId old new i)

instance Named Type where
    names = eval go
        where
            go (TyVar i) = idNamesInType i
            go (TyConApp n _) = [n]
            go (TyForAll b _) = tyBinderNamesInType b
            go _ = []

    rename old new = modify go
      where
        go :: Type -> Type
        go (TyVar i) = TyVar (renameIdInType old new i)
        go (TyConApp n ts) = TyConApp (rename old new n) ts
        go (TyForAll tb t) = TyForAll (renameTyBinderInType old new tb) t
        go t = t

    renames hm = modify go
      where
        go :: Type -> Type
        go (TyVar i) = TyVar (renamesIdInType hm i)
        go (TyConApp n ts) = TyConApp (renames hm n) ts
        go (TyForAll tb t) = TyForAll (renamesTyBinderInType hm tb) t
        go t = t

-- We don't want both modify and go to recurse on the Type's in TyBinders or Ids
-- so we introduce functions to collect or rename only the Names directly in those types
tyBinderNamesInType :: TyBinder -> [Name]
tyBinderNamesInType (NamedTyBndr i) = idNamesInType i
tyBinderNamesInType _ = []

idNamesInType :: Id -> [Name]
idNamesInType (Id n _) = [n]

renameTyBinderInType :: Name -> Name -> TyBinder -> TyBinder
renameTyBinderInType old new (NamedTyBndr i) = NamedTyBndr $ renameIdInType old new i
renameTyBinderInType _ _ tyb = tyb

renameIdInType :: Name -> Name -> Id -> Id
renameIdInType old new (Id n t) = Id (rename old new n) t

renamesTyBinderInType :: HM.HashMap Name Name -> TyBinder -> TyBinder
renamesTyBinderInType hm (NamedTyBndr i) = NamedTyBndr $ renamesIdInType hm i
renamesTyBinderInType _ tyb = tyb

renamesIdInType :: HM.HashMap Name Name -> Id -> Id
renamesIdInType hm (Id n t) = Id (renames hm n) t

instance Named Alt where
    names (Alt am e) = names am ++ names e

    rename old new (Alt am e) = Alt (rename old new am) (rename old new e)

    renames hm (Alt am e) = Alt (renames hm am) (renames hm e)

instance Named DataCon where
    names (DataCon n t ts) = n:(names t ++ concatMap names ts)

    rename old new (DataCon n t ts) =
        DataCon (rename old new n) (rename old new t) (rename old new ts)

    renames hm (DataCon n t ts) =
        DataCon (renames hm n) (renames hm t) (renames hm ts)

instance Named AltMatch where
    names (DataAlt dc i) = names dc ++ names i
    names _ = []

    rename old new (DataAlt dc i) =
        DataAlt (rename old new dc) (rename old new i)
    rename _ _ am = am

    renames hm (DataAlt dc i) =
        DataAlt (renames hm dc) (renames hm i)
    renames _ am = am

instance Named TyBinder where
    names (AnonTyBndr t) = names t
    names (NamedTyBndr i) = names i

    rename old new (AnonTyBndr t) = AnonTyBndr (rename old new t)
    rename old new (NamedTyBndr i) = NamedTyBndr (rename old new i)

    renames hm (AnonTyBndr t) = AnonTyBndr (renames hm t)
    renames hm (NamedTyBndr i) = NamedTyBndr (renames hm i)

instance Named Coercion where
    names (t1 :~ t2) = names t1 ++ names t2
    rename old new (t1 :~ t2) = rename old new t1 :~ rename old new t2
    renames hm (t1 :~ t2) = renames hm t1 :~ renames hm t2

instance Named AlgDataTy where
    names (DataTyCon ns dc) = ns ++ names dc
    names (NewTyCon ns dc rt) = ns ++ names dc ++ names rt

    rename old new (DataTyCon n dc) = DataTyCon (rename old new n) (rename old new dc)
    rename old new (NewTyCon n dc rt) = NewTyCon (rename old new n) (rename old new dc) (rename old new rt)

    renames hm (DataTyCon n dc) = DataTyCon (renames hm n) (renames hm dc)
    renames hm (NewTyCon n dc rt) = NewTyCon (renames hm n) (renames hm dc) (renames hm rt)

instance Named KnownValues where
    names (KnownValues {
              dcInt = dI
            , dcFloat = dF
            , dcDouble = dD
            , dcInteger = dI2

            , tyInt = tI
            , tyFloat = tF
            , tyDouble = tD
            , tyInteger = tI2

            , tyBool = tB
            , dcTrue = dcT
            , dcFalse = dcF

            , eqTC = eqT
            , numTC = numT
            , ordTC = ordT
            , integralTC = integralT

            , eqFunc = eqF
            , neqFunc = neqF
            , geFunc = geF
            , gtFunc = gtF
            , ltFunc = ltF
            , leFunc = leF

            , andFunc = andF
            , orFunc = orF
            }) =
            [dI, dF, dD, dI2, tI, tI2, tF, tD, tB, dcT, dcF
            , eqT, numT, ordT, integralT, eqF, neqF, geF, gtF, ltF, leF
            , andF, orF]

    rename old new (KnownValues {
                     dcInt = dI
                   , dcFloat = dF
                   , dcDouble = dD
                   , dcInteger = dI2

                   , tyInt = tI
                   , tyFloat = tF
                   , tyDouble = tD
                   , tyInteger = tI2

                   , tyBool = tB
                   , dcTrue = dcT
                   , dcFalse = dcF

                   , eqTC = eqT
                   , numTC = numT
                   , ordTC = ordT
                   , integralTC = integralT

                   , eqFunc = eqF
                   , neqFunc = neqF
                   , geFunc = geF
                   , gtFunc = gtF
                   , ltFunc = ltF
                   , leFunc = leF

                   , andFunc = andF
                   , orFunc = orF
                   }) =
                    (KnownValues {
                          dcInt = rename old new dI
                        , dcFloat = rename old new dF
                        , dcDouble = rename old new dD
                        , dcInteger = rename old new dI2

                        , tyInt = rename old new tI
                        , tyFloat = rename old new tF
                        , tyDouble = rename old new tD
                        , tyInteger = rename old new tI2

                        , tyBool = rename old new tB
                        , dcTrue = rename old new dcT
                        , dcFalse = rename old new dcF
                        , eqTC = rename old new eqT
                        , numTC = rename old new numT
                        , ordTC = rename old new ordT
                        , integralTC = rename old new integralT

                        , eqFunc = rename old new eqF
                        , neqFunc = rename old new neqF
                        , geFunc = rename old new geF
                        , gtFunc = rename old new gtF
                        , ltFunc = rename old new ltF
                        , leFunc = rename old new leF

                        , andFunc = rename old new andF
                        , orFunc = rename old new orF
                        })

instance (Foldable f, Functor f, Named a) => Named (f a) where
    names = foldMap names
    rename old new = fmap (rename old new)
    renames hm = fmap (renames hm)

instance Named () where
    names _ = []
    rename _ _ = id
    renames _ = id

instance {-# OVERLAPPING #-}  (Named s, Hashable s, Eq s) => Named (HS.HashSet s) where
    names = names . HS.toList 
    rename old new = HS.map (rename old new)
    renames hm = HS.map (renames hm)

instance {-# OVERLAPPING #-} (Named a, Named b) => Named (a, b) where
    names (a, b) = names a ++ names b
    rename old new (a, b) = (rename old new a, rename old new b)
    renames hm (a, b) = (renames hm a, renames hm b)

instance {-# OVERLAPPING #-} (Named a, Named b, Named c) => Named (a, b, c) where
    names (a, b, c) = names a ++ names b ++ names c
    rename old new (a, b, c) = (rename old new a, rename old new b, rename old new c)
    renames hm (a, b, c) = (renames hm a, renames hm b, renames hm c)

instance {-# OVERLAPPING #-} (Named a, Named b, Named c, Named d) => Named (a, b, c, d) where
    names (a, b, c, d) = names a ++ names b ++ names c ++ names d
    rename old new (a, b, c, d) = (rename old new a, rename old new b, rename old new c, rename old new d)
    renames hm (a, b, c, d) = (renames hm a, renames hm b, renames hm c, renames hm d)

instance {-# OVERLAPPING #-} (Named a, Named b, Named c, Named d, Named e) => Named (a, b, c, d, e) where
    names (a, b, c, d, e) = names a ++ names b ++ names c ++ names d ++ names e
    rename old new (a, b, c, d, e) = (rename old new a, rename old new b, rename old new c, rename old new d, rename old new e)
    renames hm (a, b, c, d, e) = (renames hm a, renames hm b, renames hm c, renames hm d, renames hm e)

freshSeededString :: T.Text -> NameGen -> (Name, NameGen)
freshSeededString t = freshSeededName (Name t Nothing 0)

freshSeededStrings :: [T.Text] -> NameGen -> ([Name], NameGen)
freshSeededStrings t = freshSeededNames (map (\t' -> Name t' Nothing 0) t)

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
