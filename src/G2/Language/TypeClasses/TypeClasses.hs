{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Language.TypeClasses.TypeClasses ( TypeClasses
                                           , Class (..)
                                           , initTypeClasses
                                           , insertClass
                                           , unionTypeClasses
                                           , isTypeClassNamed
                                           , isTypeClass
                                           , lookupTCDict
                                           , lookupTCDicts
                                           , lookupTCClass
                                           , tcWithNameMap
                                           , tcDicts
                                           , typeClassInst
                                           , satisfyingTCTypes
                                           , toMap) where

import G2.Language.AST
import G2.Language.KnownValues (KnownValues)
import G2.Language.Naming
import G2.Language.Syntax
import G2.Language.Typing

import Data.Coerce
import Data.Data (Data, Typeable)
import Data.Hashable
import Data.List
import qualified Data.Map.Lazy as MM
import qualified Data.HashMap.Lazy as M
import Data.Maybe
import qualified Data.Sequence as S
import qualified G2.Language.TyVarEnv as TV 
import GHC.Generics (Generic)

data Class = Class { insts :: [(Type, Id)], typ_ids :: [Id], superclasses :: [(Type, Id)]}
                deriving (Show, Eq, Read, Typeable, Data, Generic)

instance Hashable Class

type TCType = M.HashMap Name Class
newtype TypeClasses = TypeClasses TCType
                      deriving (Show, Eq, Read, Typeable, Data, Generic)

instance Hashable TypeClasses

initTypeClasses :: TV.TyVarEnv -> [(Name, Id, [Id], [(Type, Id)])] -> TypeClasses
initTypeClasses tv nsi =
    let
        ns = map (\(n, _, i, sc) -> (n, i, sc)) nsi
        nsi' = filter (not . null . insts . snd)
             $ map (\(n, i, sc) -> 
                (n, Class { insts = nub $ mapMaybe (nameIdToTypeId tv n) nsi
                          , typ_ids = i
                          , superclasses = sc } )) ns
    in
    coerce $ M.fromList nsi'

insertClass :: Name -> Class -> TypeClasses -> TypeClasses
insertClass n c (TypeClasses tc) = TypeClasses (M.insert n c tc)

unionTypeClasses :: TypeClasses -> TypeClasses -> TypeClasses
unionTypeClasses (TypeClasses tc) (TypeClasses tc') = TypeClasses (M.union tc tc')

nameIdToTypeId :: TV.TyVarEnv -> Name -> (Name, Id, [Id], [(Type, Id)]) -> Maybe (Type, Id)
nameIdToTypeId tv nm (n, i, _, _) =
    let
        t = affectedType $ returnType (typeOf tv i)
    in
    if n == nm then fmap (, i) t else Nothing

affectedType :: Type -> Maybe Type
affectedType (TyApp _ t) = Just t
affectedType _ = Nothing

-- | Is there a typeclass with the given `Name`?
isTypeClassNamed :: Name -> TypeClasses -> Bool
isTypeClassNamed n = M.member n . (coerce :: TypeClasses -> TCType)

-- | Is the given type a type class?
isTypeClass :: TypeClasses -> Type -> Bool
isTypeClass tc (TyCon n _) = isTypeClassNamed n tc 
isTypeClass tc (TyApp t _) = isTypeClass tc t
isTypeClass _ _ = False

-- | Returns the dictionary for the given typeclass and Type,
-- if one exists.
lookupTCDict :: TypeClasses
             -> Name -- ^ `Name` of the typeclass to look for
             -> Type -- ^ The `Type` you want a dictionary for
             -> Maybe Id
lookupTCDict tc n t =
    case fmap insts $ M.lookup n (toMap tc) of
        Just c -> fmap snd $ find (\(t', _) -> t .:: t') c
        Nothing -> Nothing

-- | Given a typeclass `Name`, gives an association list of
-- `Type`s that have instances of that typeclass, and the
-- typeclass dictionaries.
lookupTCDicts :: Name -> TypeClasses -> Maybe [(Type, Id)]
lookupTCDicts n = fmap insts . M.lookup n . coerce 

lookupTCClass :: Name -> TypeClasses -> Maybe Class
lookupTCClass n = M.lookup n . coerce

tcWithNameMap :: TV.TyVarEnv -> Name -> [Id] -> M.HashMap Name Id
tcWithNameMap tv n =
    M.fromList
        . map (\i -> (forType $ typeOf tv i, i))
        . filter (isTC . typeOf tv)
    where
        forType :: Type -> Name
        forType (TyApp _ (TyVar (Id n' _))) = n'
        forType _ = error "Bad type in forType"

        isTC :: Type -> Bool
        isTC t = case tyAppCenter t of
                        TyCon n' _ -> n == n'
                        _ -> False

-- tcDicts
tcDicts :: TypeClasses -> [Id]
tcDicts = map snd . concatMap insts . M.elems . coerce

tyConAppName :: Type -> Maybe Name
tyConAppName (TyCon n _) = Just n
tyConAppName _ = Nothing

-- Given a TypeClass name, a type that you want an instance of that typeclass
-- for, and a mapping of TyVar name's to Id's for those types instances of
-- the typeclass, returns an instance of the typeclass, if possible 
typeClassInst :: TypeClasses -> M.HashMap Name Id -> Name -> Type -> Maybe Expr 
typeClassInst tc m tcn t
    | tca@(TyCon _ _) <- tyAppCenter t
    , ts <- tyAppArgs t
    , tcs <- map (typeClassInst tc m tcn) ts
    , all isJust tcs =
        case lookupTCDict tc tcn tca of
            Just i -> Just (foldl' App (Var i) $ map Type ts ++ map fromJust tcs)
            Nothing -> Nothing
    | (TyVar (Id n _)) <- tyAppCenter t
    , ts <- tyAppArgs t
    , tcs <- map (typeClassInst tc m tcn) ts
    , all (isJust) tcs =
        case M.lookup n m of
            Just i -> Just (foldl' App (Var i) $ map Type ts ++ map fromJust tcs)
            Nothing -> Nothing
typeClassInst _ _ _ _ = Nothing

-- | Finds `Type`s that satisfy the given typeclass requirements for the given polymorphic argument.
-- Returns "Int" by default if there are no typeclass requirements.
satisfyingTCTypes :: KnownValues
                  -> TypeClasses
                  -> Id -- ^ The type variable to look for possible instantiations of 
                  -> [Type] -- ^ Function arguments to satisfy typeclass requirements for
                  -> [Type]
satisfyingTCTypes kv tc i ts =
    let
        tcReq = satisfyTCReq tc i ts
    in
    case mapMaybe lookupTCDictsTypes tcReq of
        [] -> [tyInt kv]
        xs -> substKind i $ foldr1 intersect xs
    where
        lookupTCDictsTypes (TyApp t1 t2) =
              fmap (mapMaybe (\t' -> 
                let sp = specializes t' t2
                 in trace ("Trying: " ++ show t' ++ " specializes to " ++ show sp) $
                        case sp of
                            Just m  -> trace ("Looking up: " ++ show (idName i) ++ " in " ++ show m) $
                                    TV.lookup (idName i) m
                            Nothing -> trace "Specialization failed" Nothing))
            . fmap (map fst)
            . flip lookupTCDicts tc
            =<< (tyConAppName . tyAppCenter $ t1)
        lookupTCDictsTypes _ = Nothing

substKind :: Id -> [Type] -> [Type]
substKind (Id _ t) ts = map (\t' -> case t' of 
                                        TyCon n _ -> TyCon n (tyFunToTyApp t)
                                        t'' -> t'') ts

tyFunToTyApp :: Type -> Type
tyFunToTyApp (TyFun t1 (TyFun t2 t3)) = TyApp (TyApp (tyFunToTyApp t1) (tyFunToTyApp t2)) (tyFunToTyApp t3)
tyFunToTyApp t = modifyChildren tyFunToTyApp t

-- | Finds the names of the required typeclasses for a TyVar Id
satisfyTCReq :: TypeClasses -> Id -> [Type] -> [Type]
satisfyTCReq tc (Id n _) = filter isFor . filter (isTypeClass tc)
    where
      isFor :: Type -> Bool
      isFor (TyVar (Id n' _)) = n == n'
      isFor (TyApp a1 a2) = isFor a1 || isFor a2
      isFor _ = False

toMap :: TypeClasses -> M.HashMap Name Class
toMap = coerce

instance ASTContainer TypeClasses Expr where
    containedASTs _ = []
    modifyContainedASTs _ = id

instance ASTContainer TypeClasses Type where
    containedASTs = containedASTs . (coerce :: TypeClasses -> TCType)
    modifyContainedASTs f = 
        coerce . modifyContainedASTs f . (coerce :: TypeClasses -> TCType)

instance ASTContainer Class Expr where
    containedASTs _ = []
    modifyContainedASTs _ = id

instance ASTContainer Class Type where
    containedASTs c = (containedASTs . insts $ c) ++ containedASTs (superclasses c)
    modifyContainedASTs f c = Class { insts = modifyContainedASTs f $ insts c
                                    , typ_ids = modifyContainedASTs f $ typ_ids c
                                    , superclasses = modifyContainedASTs f $ superclasses c}

instance Named TypeClasses where
    names (TypeClasses tc) = S.fromList (M.keys tc) <> names tc
    rename old new (TypeClasses m) =
        coerce $ M.mapKeys (rename old new) $ rename old new m
    renames hm (TypeClasses m) =
        coerce $ M.mapKeys (renames hm) $ renames hm m

instance Named Class where
    names (Class { insts = i, typ_ids = tids, superclasses = sc }) = names i <> names tids <> names sc
    rename old new c = Class { insts = rename old new $ insts c
                             , typ_ids = rename old new $ typ_ids c
                             , superclasses = rename old new $ superclasses c }
    renames hm c = Class { insts = renames hm $ insts c
                         , typ_ids = renames hm $ typ_ids c
                         , superclasses = renames hm $ superclasses c }
