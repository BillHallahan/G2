{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Type Checker
--   Provides type checking capabilities over G2 Language.
module G2.Language.Typing
    ( Typed (..)

    , unify
    , unify'
    
    , tyInt
    , tyInteger
    , tyDouble
    , tyFloat
    , tyBool
    , tyChar
    , tyRational
    , tyList
    , tyString
    , tyMaybe
    , tyUnit
    , mkTyApp
    , mkTyFun
    , tyAppCenter
    , tyAppArgs
    , unTyApp
    , mkTyCon
    , mkFullAppedTyCon
    , (.::)
    , (.::.)
    , specializes
    , specializes'
    , hasFuncType
    , higherOrderFuncs
    , isTYPE
    , isTyFun
    , hasTYPE
    , isTyVar
    , tyVarIds
    , tyVarNames
    , numArgs

    , replaceTyVar
    , replaceTyVars
    , applyTypeMap
    , applyTypeHashMap

    , ArgType (..)
    , argumentTypes
    , argTypeToType
    , argTypeToLamUse
    , spArgumentTypes
    , leadingTyForAllBindings
    , tyForAllBindings
    , anonArgumentTypes
    , returnType
    , splitTyForAlls
    , splitTyFuns
    , retype
    , retypeRespectingTyForAll
    , tyVarSubst
    , mapInTyForAlls
    , inTyForAlls
    , numTypeArgs
    , typeToExpr
    , getTyApps
    , tyAppsToExpr
    , isADTType
    , isPrimType
    ) where

import qualified G2.Data.UFMap as UF
import G2.Language.AST
import qualified G2.Language.KnownValues as KV
import G2.Language.Syntax

import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M
import Data.Maybe
import qualified Data.List as L
import Control.Monad
import qualified G2.Language.TyVarEnv as TV

tyInt :: KV.KnownValues -> Type
tyInt kv = TyCon (KV.tyInt kv) (tyTYPE kv)

tyInteger :: KV.KnownValues -> Type
tyInteger kv = TyCon (KV.tyInteger kv) (tyTYPE kv)

tyDouble :: KV.KnownValues -> Type
tyDouble kv = TyCon (KV.tyDouble kv) (tyTYPE kv)

tyFloat :: KV.KnownValues -> Type
tyFloat kv = TyCon (KV.tyFloat kv) (tyTYPE kv)

tyBool :: KV.KnownValues -> Type
tyBool kv = TyCon (KV.tyBool kv) (tyTYPE kv)

tyChar :: KV.KnownValues -> Type
tyChar kv = TyCon (KV.tyChar kv) (tyTYPE kv)

tyRational :: KV.KnownValues -> Type
tyRational kv = TyCon (KV.tyRational kv) (tyTYPE kv)

tyList :: KV.KnownValues -> Type
tyList kv = TyCon (KV.tyList kv) (TyFun TYPE TYPE)

tyString :: KV.KnownValues -> Type
tyString kv = TyApp (tyList kv) (tyChar kv)

tyMaybe :: KV.KnownValues -> Type
tyMaybe kv = TyCon (KV.tyMaybe kv) (TyFun TYPE TYPE)

tyUnit :: KV.KnownValues -> Type
tyUnit kv = TyCon (KV.tyUnit kv) (TyFun TYPE TYPE)

tyTYPE :: KV.KnownValues -> Type
tyTYPE _ = TYPE

-- | Turns the Expr list into an application spine
mkTyFun :: [Type] -> Type
mkTyFun [] = error "mkTyFun: empty list"
mkTyFun [t] = t
mkTyFun (t1:ts) = TyFun t1 (mkTyFun ts)

tyAppCenter :: Type -> Type
tyAppCenter (TyApp t _) = tyAppCenter t
tyAppCenter t = t

tyAppArgs :: Type -> [Type]
tyAppArgs (TyApp t t') = tyAppArgs t ++ [t']
tyAppArgs _ = []

mkTyApp :: [Type] -> Type
mkTyApp [] = TYPE
mkTyApp (t:[]) = t
mkTyApp (t1:t2:ts) = mkTyApp (TyApp t1 t2 : ts)

mkTyCon :: Name
        -> [Type]
        -> Kind
        -> Type
mkTyCon n ts k = mkTyApp $ TyCon n k:ts

-- | Makes a fully applied TyCon.
-- Since the TyCon is fully applied, we can figure out its kind based on it's
-- arguments and result kind.
mkFullAppedTyCon :: TV.TyVarEnv
                 -> Name
                 -> [Type] -- ^ Type arguments
                 -> Kind -- ^ Result kind
                 -> Type
mkFullAppedTyCon tv n ts k =
    let
        tsk = mkTyFun $ map (typeOf tv) ts ++ [k]
    in
    mkTyApp $ TyCon n tsk:ts

-- | Unravels the application spine of (nested) `TyApp`s.
unTyApp :: Type -> [Type]
unTyApp (TyApp t t') = unTyApp t ++ [t']
unTyApp t = [t]

-- | Typeclass for things that have type information.
class Typed a where
    typeOf :: TV.TyVarEnv -> a -> Type

instance Typed Id where
    typeOf m (Id _ ty) = tyVarSubst m ty

instance Typed Lit where
    typeOf _ (LitInt _) = TyLitInt
    typeOf _ (LitWord _) = TyLitWord
    typeOf _ (LitFloat _) = TyLitFloat
    typeOf _ (LitDouble _) = TyLitDouble
    typeOf _ (LitRational _) = TyLitRational
    typeOf _ (LitBV bv) = TyLitBV (length bv)
    typeOf _ (LitChar _)   = TyLitChar
    typeOf _ (LitString _) = TyLitString
    typeOf _ (LitInteger _) = TyLitInt

instance Typed DataCon where
    typeOf _ (DataCon _ ty _ _) = ty

instance Typed Alt where
    typeOf m (Alt _ expr) = typeOf m expr

instance Typed Expr where
    typeOf m (Var v) = typeOf m v
    typeOf m (Lit lit) = typeOf m lit
    typeOf _ (Prim _ ty) = ty
    typeOf m (Data dcon) = typeOf m dcon
    typeOf m a@(App _ _) =
        let
            as = passedArgs a
            t = typeOf m $ appCenter a
        in
        appTypeOf TV.empty t as
    typeOf m (Lam u b e) =
        case u of
            TypeL -> TyForAll b (typeOf m e)
            TermL -> TyFun (typeOf m b) (typeOf m e)
    typeOf m (Let _ expr) = typeOf m expr
    typeOf _ (Case _ _ t _) = t
    typeOf _ (Type _) = TYPE
    typeOf m (Cast _ (_ :~ t')) = tyVarSubst m t'
    typeOf m (Coercion (_ :~ t')) = tyVarSubst m t'
    typeOf m (Tick _ e) = typeOf m e
    typeOf m (NonDet (e:_)) = typeOf m e
    typeOf _ (NonDet []) = TyBottom
    typeOf _ (SymGen _ t) = t
    typeOf m (Assert _ _ e) = typeOf m e
    typeOf m (Assume _ _ e) = typeOf m e

passedArgs :: Expr -> [Expr]
passedArgs = reverse . passedArgs'

passedArgs' :: Expr -> [Expr]
passedArgs' (App e e') = e':passedArgs' e
passedArgs' _ = []

appCenter :: Expr -> Expr
appCenter (App a _) = appCenter a
appCenter e = e

appTypeOf :: TV.TyVarEnv -> Type -> [Expr] -> Type
appTypeOf m (TyForAll i t) (Type t':es) =
    let
        m' = TV.insert (idName i) (tyVarSubst m t') m
    in
    appTypeOf m' t es
appTypeOf m (TyForAll _ t) (_:es) = appTypeOf m t es
appTypeOf m (TyFun _ t) (_:es) = appTypeOf m t es
appTypeOf m t [] = tyVarSubst m t
appTypeOf m (TyVar (Id n _)) es =
    case TV.lookup n m of
        Just t -> appTypeOf m t es
        Nothing -> error ("appTypeOf: Unknown TyVar")
appTypeOf _ TyBottom _ = TyBottom
appTypeOf _ TyUnknown _ = TyUnknown
appTypeOf _ t es = error ("appTypeOf\n" ++ show t ++ "\n" ++ show es ++ "\n\n")

-- | Check if two types unify.  If they do, returns a `UFMap` of type variables to instantiations.
unify :: Type -> Type -> Maybe (UF.UFMap Name Type)
unify = unify' UF.empty

-- | `unify`, but with a pre-existing (partial) mapping of type variables to instantiations.
unify' :: UF.UFMap Name Type -> Type -> Type ->  Maybe (UF.UFMap Name Type)
unify' uf (TyVar (Id n1 t1)) (TyVar (Id n2 t2))
    | Just uf_t1 <- UF.lookup n1 uf
    , Just uf_t2 <- UF.lookup n2 uf =
        UF.join const n1 n2 <$> unify' uf uf_t1 uf_t2
    | otherwise =
        UF.join (error "unify': impossible, no need to join") n1 n2 <$> unify' uf t1 t2
unify' uf (TyVar (Id n _)) t
    | Just t1 <- UF.lookup n uf = unify' uf t1 t
    | otherwise = Just (UF.insert n t uf)
unify' uf t (TyVar (Id n _))
    | Just t2 <- UF.lookup n uf = unify' uf t t2
    | otherwise = Just (UF.insert n t uf)
unify' uf (TyFun t1 t2) (TyFun t1' t2') = do
    uf' <- unify' uf t1 t1'
    unify' uf' t2 t2'
unify' uf (TyApp t1 t2) (TyApp t1' t2') = do
    uf' <- unify' uf t1 t1'
    unify' uf' t2 t2'
unify' uf (TyCon n1 k1) (TyCon n2 k2) | n1 == n2 = unify' uf k1 k2
unify' uf (TyForAll (Id _ it1) t1) (TyForAll (Id _ it2) t2) = do
    uf' <- unify' uf it1 it2
    unify' uf' t1 t2
unify' uf (TyFun _ _) TYPE = Just uf
unify' uf t1 t2 | t1 == t2 = return uf
                | otherwise = Nothing

instance Typed Type where
    typeOf _ (TyVar (Id _ t)) = t
    typeOf _ (TyFun _ _) = TYPE
    typeOf m (TyApp t1 t2) =
        let
            ft = typeOf m t1
            at = typeOf m t2
        in
        case (ft, at) of
            ((TyForAll _ t2'), _) -> t2'
            ((TyFun _ t2'), _) -> t2'
            ((TyApp t1' _), _) -> t1'
            _ -> error $ "Overapplied Type\n" ++ show t1 ++ "\n" ++ show t2 ++ "\n\n" ++ show ft ++ "\n" ++ show at
    typeOf _ (TyCon _ t) = t
    typeOf m (TyForAll b t) = TyApp (typeOf m b) (typeOf m t)
    typeOf _ TyLitInt = TYPE
    typeOf _ (TyLitFP _ _) = TYPE
    typeOf _ TyLitRational = TYPE
    typeOf _ (TyLitBV _) = TYPE
    typeOf _ TyLitChar = TYPE
    typeOf _ TyLitString = TYPE
    typeOf _ TYPE = TYPE
    typeOf _ TyBottom = TyBottom
    typeOf _ TyUnknown = TyUnknown

-- | Retyping
-- We look to see if the type we potentially replace has a TyVar whose Id is a
-- match on the target key that we want to replace.
retype :: (ASTContainer m Type, Show m) => Id -> Type -> m -> m
retype key new e = modifyContainedASTs (retype' key new) $ e

retype' :: Id -> Type -> Type -> Type
retype' key new (TyVar test) = if key == test then new else TyVar test
retype' key new ty = modifyChildren (retype' key new) ty

retypeRespectingTyForAll :: (ASTContainer m Type, Show m) => Id -> Type -> m -> m
retypeRespectingTyForAll key new = modifyContainedASTs (retypeRespectingTyForAll' key new)

retypeRespectingTyForAll' :: Id -> Type -> Type -> Type
retypeRespectingTyForAll' i _ t@(TyForAll ni _) | i == ni = t
retypeRespectingTyForAll' key new (TyVar test) = if idName key == idName test then new else TyVar test
retypeRespectingTyForAll' key new ty = modifyChildren (retypeRespectingTyForAll' key new) ty

tyVarSubst :: (ASTContainer t Type) => TV.TyVarEnv -> t -> t
tyVarSubst m = modifyContainedASTs (tyVarSubst' HS.empty m)

tyVarSubst' ::  HS.HashSet Name -> TV.TyVarEnv -> Type -> Type 
tyVarSubst' seen m t@(TyVar (Id n _)) =
    case TV.lookup n m of
        Just t' | not (HS.member n seen) -> tyVarSubst' (HS.insert n seen) m t'
        _ -> t 
tyVarSubst' seen m (TyForAll i@(Id n _) t) = TyForAll i $ tyVarSubst' seen (TV.delete n m) t
tyVarSubst' seen m t = modifyChildren (tyVarSubst' seen m) t

-- | Returns if the first type given is a specialization of the second,
-- i.e. if given t1, t2, returns true iff t1 :: t2
(.::) :: Type -> Type -> Bool
t1 .:: t2 = isJust $ specializes t1 t2
{-# INLINE (.::) #-}

-- | Checks if the first type is equivalent to the second type.
-- That is, @e@ has type @t1@ iff @e@ has type @t2@.
(.::.) :: Type -> Type -> Bool
t1 .::. t2 = t1 .:: t2 && t2 .:: t1
{-# INLINE (.::.) #-}

specializes :: Type -> Type -> Maybe TV.TyVarEnv 
specializes = specializes' TV.empty 

specializes' :: TV.TyVarEnv -> Type -> Type -> Maybe TV.TyVarEnv 
specializes' m _ TYPE = Just m
specializes' m t (TyVar (Id n vt)) =
    case TV.lookup n m of
        Just t' | t == t' -> Just m
                | otherwise -> Nothing
        Nothing -> TV.insert n t <$> specializes' m (typeOf m t) vt
specializes' m (TyFun t1 t2) (TyFun t1' t2') = do
    m' <- specializes' m t1 t1'
    specializes' m' t2 t2'
specializes' m (TyApp t1 t2) (TyApp t1' t2') = do
    m' <- specializes' m t1 t1'
    specializes' m' t2 t2'
specializes' m (TyCon n _) (TyCon n' _) = if n == n' then Just m else Nothing
specializes' m (TyForAll (Id _ t1) t2) (TyForAll  (Id _ t1') t2') = do
    m' <- specializes' m t1 t1'
    specializes' m' t2 t2'
specializes' m t (TyForAll _ t') =
  specializes' m t t'
specializes' m TyUnknown _ = Just m
specializes' m _ TyUnknown = Just m
specializes' m TyBottom _ = Just m
specializes' _ _ TyBottom = Nothing
specializes' m t1 t2 = if t1 == t2 then Just m else Nothing

replaceTyVar :: ASTContainer e Type => Name -> Type -> e -> e
replaceTyVar n t = modifyASTs (replaceTyVar' n t)

replaceTyVar' :: Name -> Type -> Type -> Type
replaceTyVar' n t  (TyVar (Id n' _)) | n == n' = t
replaceTyVar' _ _ t = t

replaceTyVars :: ASTContainer e Type => HM.HashMap Name Type -> e -> e
replaceTyVars m = modifyASTs (replaceTyVars' m)

replaceTyVars' ::HM.HashMap Name Type -> Type -> Type
replaceTyVars' m (TyVar (Id n _)) | Just t <- HM.lookup n m = t
replaceTyVars' _ t = t

applyTypeMap :: ASTContainer e Type => TV.TyVarEnv -> e -> e
applyTypeMap m = modifyASTs (applyTypeMap' m)

applyTypeMap' :: TV.TyVarEnv -> Type -> Type
applyTypeMap' m (TyVar (Id n _))
    | Just t <- TV.lookup n m = t
applyTypeMap' _ t = t

applyTypeHashMap :: ASTContainer e Type => HM.HashMap Name Type -> e -> e
applyTypeHashMap m = modifyASTs (applyTypeHashMap' m)

applyTypeHashMap' :: HM.HashMap Name Type -> Type -> Type
applyTypeHashMap' m (TyVar (Id n _))
    | Just t <- HM.lookup n m = t
applyTypeHashMap' _ t = t


hasFuncType :: Type -> Bool
hasFuncType t =
    case t of
        (TyFun _ _) -> True
        (TyForAll _ _)  -> True
        _ -> False

-- | higherOrderFuncs
-- Returns all internal higher order function types
higherOrderFuncs :: Type -> [Type]
higherOrderFuncs = higherOrderFuncs'

higherOrderFuncs' :: Type -> [Type]
higherOrderFuncs' = eval higherOrderFuncs''

higherOrderFuncs'' :: Type -> [Type]
higherOrderFuncs'' (TyFun t@(TyFun _ _) _) = [t]
higherOrderFuncs'' _ = []

isTYPE :: Type -> Bool
isTYPE TYPE = True
isTYPE (TyCon (Name "TYPE" _ _ _) _) = True
isTYPE _ = False

hasTYPE :: Type -> Bool
hasTYPE TYPE = True
hasTYPE (TyCon (Name "TYPE" _ _ _) _) = True
hasTYPE (TyFun t t') = hasTYPE t || hasTYPE t'
hasTYPE (TyApp t t') = hasTYPE t || hasTYPE t'
hasTYPE _ = False

isTyVar :: Type -> Bool
isTyVar (TyVar _) = True
isTyVar _ = False

isTyFun :: Type -> Bool
isTyFun (TyFun _ _) = True
isTyFun _ = False

-- | Returns a list of all tyVars Ids
tyVarIds :: ASTContainer m Type => m -> [Id]
tyVarIds = evalASTs tyVarIds'

tyVarIds' :: Type -> [Id]
tyVarIds' (TyVar i) = [i]
tyVarIds' _ = []

-- | Returns a list of all tyVars Names
tyVarNames :: ASTContainer m Type => m -> [Name]
tyVarNames = map idName . tyVarIds

-- | Computes the number of type and value level arguments 
numArgs :: Type -> Int
numArgs = length . argumentTypes

data ArgType = AnonType Type | NamedType Id deriving (Show, Read)

-- | Gives the types of the arguments of the functions
argumentTypes :: Type -> [Type]
argumentTypes = argumentTypes'

argumentTypes' :: Type -> [Type]
argumentTypes' (TyForAll _ t2) = TYPE:argumentTypes' t2
argumentTypes' (TyFun t1 t2) = t1:argumentTypes' t2
argumentTypes' _ = []

argTypeToType :: ArgType -> Type
argTypeToType (AnonType t) = t
argTypeToType (NamedType i) = TyVar i

argTypeToLamUse :: ArgType -> LamUse
argTypeToLamUse (AnonType _) = TermL
argTypeToLamUse (NamedType _) = TypeL

spArgumentTypes :: Type -> [ArgType]
spArgumentTypes = spArgumentTypes' 

spArgumentTypes' :: Type -> [ArgType]
spArgumentTypes' (TyForAll i t2) = NamedType i:spArgumentTypes' t2
spArgumentTypes' (TyFun t1 t2) = AnonType t1:spArgumentTypes' t2
spArgumentTypes' _ = []

leadingTyForAllBindings :: Type -> [Id]
leadingTyForAllBindings = leadingTyForAllBindings' 

leadingTyForAllBindings' :: Type -> [Id]
leadingTyForAllBindings' (TyForAll i t) = i:leadingTyForAllBindings' t
leadingTyForAllBindings' _ = []

tyForAllBindings :: Type -> [Id]
tyForAllBindings = tyForAllBindings'

tyForAllBindings' :: Type -> [Id]
tyForAllBindings' (TyForAll i t) = i:tyForAllBindings' t
tyForAllBindings' (TyFun t t') = tyForAllBindings' t ++ tyForAllBindings t'
tyForAllBindings' _ = []

anonArgumentTypes :: Type -> [Type]
anonArgumentTypes = anonArgumentTypes'

anonArgumentTypes' :: Type -> [Type]
anonArgumentTypes' (TyForAll _ t) = anonArgumentTypes' t
anonArgumentTypes' (TyFun t1 t2) = t1:anonArgumentTypes' t2
anonArgumentTypes' _ = []

-- | Gives the return type if the given function type is fully saturated
returnType :: Type -> Type
returnType = returnType'

returnType' :: Type -> Type
returnType' (TyForAll _ t) = returnType' t
returnType' (TyFun _ t) = returnType' t
returnType' t = t

-- | Turns TyForAll types into a list of type ids
splitTyForAlls :: Type -> ([Id], Type)
splitTyForAlls (TyForAll i t) =
    let
        (i', t') = splitTyForAlls t
    in
    (i:i', t')
splitTyForAlls t = ([], t)

-- | Turns TyFun types into a list of types
splitTyFuns :: Type -> [Type]
splitTyFuns (TyFun t t') = t:splitTyFuns t'
splitTyFuns t = [t]

-- | Nests a new type in TyForAlls
mapInTyForAlls :: (Type -> Type) -> Type -> Type
mapInTyForAlls f (TyForAll b t) = TyForAll b $ mapInTyForAlls f t
mapInTyForAlls f t = f t

-- | Extracts the type inside TyForAlls, recursively
inTyForAlls :: Type -> Type
inTyForAlls (TyForAll _ t) = inTyForAlls t
inTyForAlls t = t

numTypeArgs :: Type -> Int
numTypeArgs = numTypeArgs'

numTypeArgs' :: Type -> Int
numTypeArgs' (TyForAll _ t) = 1 + numTypeArgs' t
numTypeArgs' _ = 0

-- | Converts nested TyApps into a list of Expr-level Types
typeToExpr :: Type -> [Expr]
typeToExpr (TyApp f t) = [Type t] ++ (typeToExpr f)
typeToExpr _ = []

-- | Find nested tyApps, if any, in the given Type
getTyApps :: Type -> Maybe Type
getTyApps (TyForAll _ t) = getTyApps t
getTyApps (TyFun t _) = getTyApps t
getTyApps t@(TyApp _ _) = Just t
getTyApps _ = Nothing

-- | Given sequence of nested tyApps e.g. tyApp (tyApp ...) ...), returns list of expr level Types, searching through [Id,Type] list in the process
tyAppsToExpr :: Type -> [(Id, Type)] -> [Expr]
tyAppsToExpr (TyApp t (TyVar tVarId)) bindings = exprs ++ newTyExpr
    where
        newTyExpr = 
            case (L.find (\(i, _) -> (tVarId == i)) bindings) of -- search list of (Id, Type) to find corresponding Type, and convert to expr
                (Just (_, ty)) -> [Type ty]
                Nothing -> []
        exprs = tyAppsToExpr t bindings
tyAppsToExpr (TyApp t1 t2) bindings = exprs ++ newTyExpr
    where
        newTyExpr = [Type t2]
        exprs = tyAppsToExpr t1 bindings
tyAppsToExpr _ _ = []
 
-- | Returns True if Type represents an ADT
isADTType :: Type -> Bool
isADTType t =
    let tCenter = tyAppCenter t
    in case tCenter of
        (TyCon _ _) -> True
        _ -> False

isPrimType :: Type -> Bool
isPrimType TyLitInt = True
isPrimType TyLitWord = True
isPrimType (TyLitFP _ _) = True
isPrimType TyLitRational = True
isPrimType (TyLitBV _) = True
isPrimType TyLitChar = True
isPrimType TyLitString = True
isPrimType _ = False
