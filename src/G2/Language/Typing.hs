{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Type Checker
--   Provides type checking capabilities over G2 Language.
module G2.Language.Typing
    ( Typed (..)
    , PresType (..)
    , tyInt
    , tyInteger
    , tyDouble
    , tyFloat
    , tyBool
    , tyChar
    , tyRational
    , tyList
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
    , appendType
    , higherOrderFuncs
    , isTYPE
    , isTyFun
    , hasTYPE
    , isTyVar
    , hasTyBottom
    , tyVars
    , tyVarIds
    , tyVarNames
    , hasTyFuns
    , isPolyFunc
    , isPolyType
    , numArgs
    , ArgType (..)
    , argumentTypes
    , argTypeToType
    , argTypeToLamUse
    , spArgumentTypes
    , leadingTyForAllBindings
    , tyForAllBindings
    , anonArgumentTypes
    , returnType
    , polyIds
    , splitTyForAlls
    , splitTyFuns
    , retypeSelective
    , retype
    , retypeOutsideTyForAll
    , mapInTyForAlls
    , inTyForAlls
    , numTypeArgs
    , typeToExpr
    , getTyApps
    , tyAppsToExpr
    , isADTType
    , isPrimType
    ) where

import G2.Language.AST
import qualified G2.Language.KnownValues as KV
import G2.Language.Syntax

import qualified Data.Map as M
import qualified Data.List as L
import Data.Monoid hiding (Alt)

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

tyMaybe :: KV.KnownValues -> Type
tyMaybe kv = TyCon (KV.tyMaybe kv) (TyFun TYPE TYPE)

tyUnit :: KV.KnownValues -> Type
tyUnit kv = TyCon (KV.tyUnit kv) (TyFun TYPE TYPE)

tyTYPE :: KV.KnownValues -> Type
tyTYPE _ = TYPE

-- | mkTyFun
-- Turns the Expr list into an application spine
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
mkFullAppedTyCon :: Name
                 -> [Type] -- ^ Type arguments
                 -> Kind -- ^ Result kind
                 -> Type
mkFullAppedTyCon n ts k =
    let
        tsk = mkTyFun $ map typeOf ts ++ [k]
    in
    mkTyApp $ TyCon n tsk:ts

-- | unTyApp
-- Unravels the application spine.
unTyApp :: Type -> [Type]
unTyApp (TyApp t t') = unTyApp t ++ [t']
unTyApp t = [t]

-- | Typed typeclass.
class Typed a where
    typeOf :: a -> Type
    typeOf = typeOf' M.empty

    typeOf' :: M.Map Name Type -> a -> Type

instance Typed Id where
    typeOf' m (Id _ ty) = tyVarRename m ty

instance Typed Lit where
    typeOf (LitInt _) = TyLitInt
    typeOf (LitFloat _) = TyLitFloat
    typeOf (LitDouble _) = TyLitDouble
    typeOf (LitChar _)   = TyLitChar
    typeOf (LitString _) = TyLitString
    typeOf (LitInteger _) = TyLitInt

    typeOf' _ t = typeOf t

instance Typed DataCon where
    typeOf' _ (DataCon _ ty) = ty

instance Typed Alt where
    typeOf' m (Alt _ expr) = typeOf' m expr

instance Typed Expr where
    typeOf' m (Var v) = typeOf' m v
    typeOf' m (Lit lit) = typeOf' m lit
    typeOf' _ (Prim _ ty) = ty
    typeOf' m (Data dcon) = typeOf' m dcon
    typeOf' m a@(App _ _) =
        let
            as = passedArgs a
            t = typeOf' m $ appCenter a
        in
        appTypeOf M.empty t as
    typeOf' m (Lam u b e) =
        case u of
            TypeL -> TyForAll (NamedTyBndr b) (typeOf' m e)
            TermL -> TyFun (typeOf' m b) (typeOf' m e)
    typeOf' m (Let _ expr) = typeOf' m expr
    typeOf' m (Case _ _ (a:_)) = typeOf' m a
    typeOf' _ (Case _ _ []) = TyBottom
    typeOf' _ (Type _) = TYPE
    typeOf' m (Cast _ (_ :~ t')) = tyVarRename m t'
    typeOf' m (Coercion (_ :~ t')) = tyVarRename m t'
    typeOf' m (Tick _ e) = typeOf' m e
    typeOf' m (NonDet (e:_)) = typeOf' m e
    typeOf' _ (NonDet []) = TyBottom
    typeOf' _ (SymGen t) = t
    typeOf' m (Assert _ _ e) = typeOf' m e
    typeOf' m (Assume _ _ e) = typeOf' m e

passedArgs :: Expr -> [Expr]
passedArgs = reverse . passedArgs'

passedArgs' :: Expr -> [Expr]
passedArgs' (App e e') = e':passedArgs' e
passedArgs' _ = []

appCenter :: Expr -> Expr
appCenter (App a _) = appCenter a
appCenter e = e

appTypeOf :: M.Map Name Type -> Type -> [Expr] -> Type
appTypeOf m (TyForAll (NamedTyBndr i) t) (Type t':es) =
    let
        m' = M.insert (idName i) (tyVarRename m t') m
    in
    appTypeOf m' t es
appTypeOf m (TyForAll (NamedTyBndr _) t) (_:es) = appTypeOf m t es
appTypeOf m (TyFun _ t) (_:es) = appTypeOf m t es
appTypeOf m t [] = tyVarRename m t
appTypeOf m (TyVar (Id n _)) es =
    case M.lookup n m of
        Just t -> appTypeOf m t es
        Nothing -> error ("appTypeOf: Unknown TyVar")
appTypeOf _ TyBottom _ = TyBottom
appTypeOf _ TyUnknown _ = TyUnknown
appTypeOf _ t es = error ("appTypeOf\n" ++ show t ++ "\n" ++ show es ++ "\n\n")

instance Typed Type where
    typeOf' _ (TyVar (Id _ t)) = t
    typeOf' _ (TyFun _ _) = TYPE
    typeOf' m (TyApp t1 t2) =
        let
            ft = typeOf' m t1
            at = typeOf' m t2
        in
        case (ft, at) of
            ((TyFun _ t2'), _) -> t2'
            ((TyApp t1' _), _) -> t1'
            _ -> error $ "Overapplied Type\n" ++ show t1 ++ "\n" ++ show t2 ++ "\n\n" ++ show ft ++ "\n" ++ show at
    typeOf' _ (TyCon _ t) = t
    typeOf' m (TyForAll (NamedTyBndr b) t) = TyApp (typeOf b) (typeOf' m t)
    typeOf' m (TyForAll _ t) = typeOf' m t
    typeOf' _ TyLitInt = TYPE
    typeOf' _ TyLitFloat = TYPE
    typeOf' _ TyLitDouble = TYPE
    typeOf' _ TyLitChar = TYPE
    typeOf' _ TyLitString = TYPE
    typeOf' _ TYPE = TYPE
    typeOf' _ TyBottom = TyBottom
    typeOf' _ TyUnknown = TyUnknown

newtype PresType = PresType Type deriving (Show, Read)

instance Typed PresType where
    typeOf' _ (PresType t) = t

-- | Retypes Types in Vars, Type Expr's, Coercions, and Casts
retypeSelective :: (ASTContainer m Expr, Show m) => Id -> Type -> m -> m
retypeSelective key new e = modifyASTs (retypeSelective' key new) $ e

retypeSelective' :: Id -> Type -> Expr -> Expr
retypeSelective' i t (Var v) = Var (retype i t v)
retypeSelective' i t (Type t') = Type (retype' i t t')
retypeSelective' i t (Cast e c) = Cast e (retype i t c)
retypeSelective' i t (Coercion c) = Coercion (retype i t c)
retypeSelective' _ _ e = e

-- | Retyping
-- We look to see if the type we potentially replace has a TyVar whose Id is a
-- match on the target key that we want to replace.
retype :: (ASTContainer m Type, Show m) => Id -> Type -> m -> m
retype key new e = modifyContainedASTs (retype' key new) $ e

retype' :: Id -> Type -> Type -> Type
retype' key new (TyVar test) = if key == test then new else TyVar test
retype' key new ty = modifyChildren (retype' key new) ty

retypeOutsideTyForAll :: (ASTContainer m Type, Show m) => Id -> Type -> m -> m
retypeOutsideTyForAll key new e = modifyContainedASTs (retypeOutsideTyForAll' key new) $ e

retypeOutsideTyForAll' :: Id -> Type -> Type -> Type
retypeOutsideTyForAll' _ _ t@(TyForAll _ _) = t
retypeOutsideTyForAll' key new (TyVar test) = if key == test then new else TyVar test
retypeOutsideTyForAll' key new ty = modifyChildren (retypeOutsideTyForAll' key new) ty

tyVarRename :: (ASTContainer t Type) => M.Map Name Type -> t -> t
tyVarRename m = modifyASTs (tyVarRename' m)

tyVarRename' :: M.Map Name Type -> Type -> Type
tyVarRename' m t@(TyVar (Id n _)) = M.findWithDefault t n m
tyVarRename' _ t = t

-- | Returns if the first type given is a specialization of the second,
-- i.e. if given t1, t2, returns true iff t1 :: t2
(.::) :: Typed t => t -> Type -> Bool
t1 .:: t2 = fst $ specializes (typeOf t1) t2
{-# INLINE (.::) #-}

-- | Checks if the first type is equivalent to the second type.
-- That is, @e@ has type @t1@ iff @e@ has type @t2@.
(.::.) :: Type -> Type -> Bool
t1 .::. t2 = PresType t1 .:: t2 && PresType t2 .:: t1
{-# INLINE (.::.) #-}

specializes :: Type -> Type -> (Bool, M.Map Name Type)
specializes = specializes' M.empty

specializes' :: M.Map Name Type -> Type -> Type -> (Bool, M.Map Name Type)
specializes' m _ TYPE = (True, m)
specializes' m t (TyVar (Id n _)) =
    case M.lookup n m of
        Just (TyVar _) -> (True, m)
        Just t' -> specializes' m t t'
        Nothing -> (True, M.insert n t m)
specializes' m (TyFun t1 t2) (TyFun t1' t2') =
    let
        (b1, m') = specializes' m t1 t1'
        (b2, m'') = specializes' m' t2 t2'
    in
    (b1 && b2, m'')
specializes' m (TyApp t1 t2) (TyApp t1' t2') =
    let
        (b1, m') = specializes' m t1 t1'
        (b2, m'') = specializes' m' t2 t2'
    in
    (b1 && b2, m'')
specializes' m (TyCon n _) (TyCon n' _) = (n == n', m)
specializes' m (TyFun t1 t2) (TyForAll (AnonTyBndr t1') t2') =
  let
      (b1, m') = specializes' m t1 t1'
      (b2, m'') = specializes' m' t2 t2'
  in (b1 && b2, m'')
specializes' m (TyFun t1 t2) (TyForAll (NamedTyBndr _) t2') =
  specializes' m (TyFun t1 t2) t2'
specializes' m (TyForAll (AnonTyBndr t1) t2) (TyFun t1' t2') =
  let
      (b1, m') = specializes' m t1 t1'
      (b2, m'') = specializes' m' t2 t2'
  in (b1 && b2, m'')
specializes' m (TyForAll (AnonTyBndr t1) t2) (TyForAll (AnonTyBndr t1') t2') =
  let
      (b1, m') = specializes' m t1 t1'
      (b2, m'') = specializes' m' t2 t2'
  in (b1 && b2, m'')
specializes' m (TyForAll (AnonTyBndr t1) t2) (TyForAll (NamedTyBndr _) t2') =
  specializes' m (TyForAll (AnonTyBndr t1) t2) t2'
specializes' m (TyForAll (NamedTyBndr (Id _ t1)) t2) (TyForAll (NamedTyBndr (Id _ t1')) t2') =
  let
      (b1, m') = specializes' m t1 t1'
      (b2, m'') = specializes' m' t2 t2'
  in (b1 && b2, m'')
specializes' m t (TyForAll _ t') =
  specializes' m t t'
specializes' m TyUnknown _ = (True, m)
specializes' m _ TyUnknown = (True, m)
specializes' m TyBottom _ = (True, m)
specializes' m _ TyBottom = (False, m)
specializes' m t1 t2 = (t1 == t2, m)

hasFuncType :: (Typed t) => t -> Bool
hasFuncType t =
    case typeOf t of
        (TyFun _ _) -> True
        (TyForAll _ _)  -> True
        _ -> False

-- | appendType
-- Converts the (function) type t1 to return t2
-- appendType (a -> b) c = (a -> b -> c)
appendType :: Type -> Type -> Type
appendType (TyFun t t1) t2 = TyFun t (appendType t1 t2)
appendType t1 t2 = TyFun t1 t2

-- | higherOrderFuncs
-- Returns all internal higher order function types
higherOrderFuncs :: Typed t => t -> [Type]
higherOrderFuncs = higherOrderFuncs' . typeOf

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

-- | isPolyFunc
-- Checks if the given function is a polymorphic function
isPolyFunc ::  Typed t => t -> Bool
isPolyFunc = isPolyFunc' . typeOf

isPolyFunc' :: Type -> Bool
isPolyFunc' (TyForAll _ _) = True
isPolyFunc' _ = False


-- | Checks if the given type is polymorphic
isPolyType :: Typed t => t -> Bool
isPolyType = not . null . tyVars . typeOf

-- tyVars
-- Returns a list of all tyVars
tyVars :: ASTContainer m Type => m -> [Type]
tyVars = evalASTs tyVars'

tyVars' :: Type -> [Type]
tyVars' t@(TyVar _) = [t]
tyVars' _ = []

-- | Returns a list of all tyVars Ids
tyVarIds :: ASTContainer m Type => m -> [Id]
tyVarIds = evalASTs tyVarIds'

tyVarIds' :: Type -> [Id]
tyVarIds' (TyVar i) = [i]
tyVarIds' _ = []

-- | Returns a list of all tyVars Names
tyVarNames :: ASTContainer m Type => m -> [Name]
tyVarNames = map idName . tyVarIds

-- | hasTyFuns
hasTyFuns :: ASTContainer m Type => m -> Bool
hasTyFuns = getAny . evalASTs hasTyFuns'

hasTyFuns' :: Type -> Any
hasTyFuns' (TyFun _ _) = Any True
hasTyFuns' _ = Any False

-- hasTyBottom
hasTyBottom :: ASTContainer m Type => m -> Bool
hasTyBottom = getAny . evalASTs hasTyBottom'

hasTyBottom' :: Type -> Any
hasTyBottom' TyBottom = Any True
hasTyBottom' _ = Any False

-- | numArgs
numArgs :: Typed t => t -> Int
numArgs = length . argumentTypes

data ArgType = AnonType Type | NamedType Id deriving (Show, Read)

-- | Gives the types of the arguments of the functions
argumentTypes :: Typed t => t -> [Type]
argumentTypes = argumentTypes' . typeOf

argumentTypes' :: Type -> [Type]
argumentTypes' (TyForAll (AnonTyBndr t1) t2) = t1:argumentTypes' t2
argumentTypes' (TyForAll (NamedTyBndr _) t2) = TYPE:argumentTypes' t2
argumentTypes' (TyFun t1 t2) = t1:argumentTypes' t2
argumentTypes' _ = []

argTypeToType :: ArgType -> Type
argTypeToType (AnonType t) = t
argTypeToType (NamedType i) = TyVar i

argTypeToLamUse :: ArgType -> LamUse
argTypeToLamUse (AnonType _) = TermL
argTypeToLamUse (NamedType _) = TypeL

spArgumentTypes :: Typed t => t -> [ArgType]
spArgumentTypes = spArgumentTypes' . typeOf

spArgumentTypes' :: Type -> [ArgType]
spArgumentTypes' (TyForAll (AnonTyBndr t1) t2) = AnonType t1:spArgumentTypes' t2
spArgumentTypes' (TyForAll (NamedTyBndr i) t2) = NamedType i:spArgumentTypes' t2
spArgumentTypes' (TyFun t1 t2) = AnonType t1:spArgumentTypes' t2
spArgumentTypes' _ = []

leadingTyForAllBindings :: Typed t => t -> [Id]
leadingTyForAllBindings = leadingTyForAllBindings' . typeOf

leadingTyForAllBindings' :: Type -> [Id]
leadingTyForAllBindings' (TyForAll (NamedTyBndr i) t) = i:leadingTyForAllBindings' t
leadingTyForAllBindings' _ = []

tyForAllBindings :: Typed t => t -> [Id]
tyForAllBindings = tyForAllBindings' . typeOf

tyForAllBindings' :: Type -> [Id]
tyForAllBindings' (TyForAll (NamedTyBndr i) t) = i:tyForAllBindings' t
tyForAllBindings' (TyForAll _ t) = tyForAllBindings' t
tyForAllBindings' (TyFun t t') = tyForAllBindings' t ++ tyForAllBindings t'
tyForAllBindings' _ = []

anonArgumentTypes :: Typed t => t -> [Type]
anonArgumentTypes = anonArgumentTypes' . typeOf

anonArgumentTypes' :: Type -> [Type]
anonArgumentTypes' (TyForAll _ t) = anonArgumentTypes' t
anonArgumentTypes' (TyFun t1 t2) = t1:anonArgumentTypes' t2
anonArgumentTypes' _ = []

-- | Gives the return type if the given function type is fully saturated
returnType :: Typed t => t -> Type
returnType = returnType' . typeOf

returnType' :: Type -> Type
returnType' (TyForAll _ t) = returnType' t
returnType' (TyFun _ t) = returnType' t
returnType' t = t

-- | Returns all polymorphic Ids in the given type
polyIds :: Type -> [Id]
polyIds = fst . splitTyForAlls

-- | Turns TyForAll types into a list of type ids
splitTyForAlls :: Type -> ([Id], Type)
splitTyForAlls (TyForAll (NamedTyBndr i) t) =
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

numTypeArgs :: Typed t => t -> Int
numTypeArgs = numTypeArgs' . typeOf

numTypeArgs' :: Type -> Int
numTypeArgs' (TyForAll (NamedTyBndr _) t) = 1 + numTypeArgs' t
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
isPrimType TyLitFloat = True
isPrimType TyLitDouble = True
isPrimType TyLitChar = True
isPrimType TyLitString = True
isPrimType _ = False
