{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Type Checker
--   Provides type checking capabilities over G2 Language.
module G2.Internals.Language.Typing
    ( Typed (..)
    , PresType (..)
    , tyInt
    , tyInteger
    , tyDouble
    , tyFloat
    , tyBool
    , mkTyApp
    , mkTyFun
    , (.::)
    , (.::.)
    , specializes
    , hasFuncType
    , appendType
    , higherOrderFuncs
    , isAlgDataTy
    , isTYPE
    , isTyFun
    , hasTYPE
    , isTyVar
    , hasTyBottom
    , tyVars
    , isPolyFunc
    , numArgs
    , ArgType (..)
    , argumentTypes
    , spArgumentTypes
    , tyForAllBindings
    , nonTyForAllArgumentTypes
    , returnType
    , polyIds
    , splitTyForAlls
    , splitTyFuns
    , retype
    , nestTyForAlls
    , inTyForAlls
    , collapseTyConApp
    ) where

import G2.Internals.Language.AST
import qualified G2.Internals.Language.KnownValues as KV
import G2.Internals.Language.Syntax

import qualified Data.Map as M
import Data.Monoid hiding (Alt)

tyInt :: KV.KnownValues -> Type
tyInt kv = TyConApp (KV.tyInt kv) []

tyInteger :: KV.KnownValues -> Type
tyInteger kv = TyConApp (KV.tyInteger kv) []

tyDouble :: KV.KnownValues -> Type
tyDouble kv = TyConApp (KV.tyDouble kv) []

tyFloat :: KV.KnownValues -> Type
tyFloat kv = TyConApp (KV.tyFloat kv) []

tyBool :: KV.KnownValues -> Type
tyBool kv = TyConApp (KV.tyBool kv) []

mkTyApp :: Type -> Type -> Type
mkTyApp (TyConApp n ts) t2 = TyConApp n $ ts ++ [t2]
mkTyApp (TyFun _ t2) _ = t2
mkTyApp t1 t2 = TyApp t1 t2

-- | mkTyFun
-- Turns the Expr list into an application spine
mkTyFun :: [Type] -> Type
mkTyFun [] = error "mkTyFun: empty list"
mkTyFun [t] = t
mkTyFun (t1:ts) = TyFun t1 (mkTyFun ts)
-- mkTyFun (t:[]) = t
-- mkTyFun (t1:t2:ts) = mkTyFun (TyFun t1 t2 : ts)

-- | unTyApp
-- Unravels the application spine.
unTyApp :: Type -> [Type]
unTyApp (TyApp t t') = unTyApp t ++ [t']
unTyApp t = [t]

-- | Typed typeclass.
class Typed a where
    typeOf :: a -> Type
    typeOf = fst . typeOf' M.empty

    typeOf' :: M.Map Name Type -> a -> (Type, M.Map Name Type)

-- | `Id` instance of `Typed`.
instance Typed Id where
    typeOf' m (Id _ ty) = typeOf' m ty

-- | `Primitive` instance of `Typed`
-- | `Lit` instance of `Typed`.
instance Typed Lit where
    typeOf (LitInt _) = TyLitInt
    typeOf (LitFloat _) = TyLitFloat
    typeOf (LitDouble _) = TyLitDouble
    typeOf (LitChar _)   = TyLitChar
    typeOf (LitString _) = TyLitString
    typeOf (LitInteger _) = TyLitInt

    typeOf' m t = (typeOf t, m)

-- | `DataCon` instance of `Typed`.
instance Typed DataCon where
    typeOf' m (DataCon _ ty _) = (ty, m)

-- | `Alt` instance of `Typed`.
instance Typed Alt where
    typeOf' m (Alt _ expr) = typeOf' m expr

-- | `Expr` instance of `Typed`.
instance Typed Expr where
    typeOf' m (Var v) = typeOf' m v
    typeOf' m (Lit lit) = typeOf' m lit
    typeOf' m (Prim _ ty) = (ty, m)
    typeOf' m (Data dcon) = typeOf' m dcon
    typeOf' m (App fxpr axpr) =
        let
            (tfxpr, m') = typeOf' m fxpr
            (taxpr, m'') = typeOf' m' axpr
        in
        case (tfxpr, taxpr) of
            (TyForAll (NamedTyBndr i) t2, _) -> 
                let
                    t2' = replaceASTs (TyVar i) taxpr t2--M.insert (idName i) taxpr m''
                    m''' = M.insert (idName i) taxpr m''
                in
                typeOf' m''' t2'
            (TyFun (TyVar (Id n _)) t2, tca@(TyConApp _ _)) ->
                let
                    m''' = M.insert n tca m''
                in
                typeOf' m''' t2
            (TyFun _ t2, _) -> (t2, m'')  -- if t1 == tfxpr then t2 else TyBottom -- TODO:
                               -- We should really have this if check- but
                               -- can't because of TyBottom being introduced
                               -- elsewhere...
            _ -> (TyBottom, m'')
    typeOf' m (Lam b expr) =
        let
            (t1, m') = case typeOf' m b of
                (TYPE, _m) -> (TyForAll (NamedTyBndr b), _m)
                (TyConApp (Name "TYPE" _ _ ) _, _m) -> (TyForAll (NamedTyBndr b), _m)
                (TyFun TYPE _, _m) -> (TyForAll (NamedTyBndr b), _m)
                (t, _m) -> (TyFun t, m)
            (t2, m'') = typeOf' m' expr
        in
        (t1 t2, m'')
    typeOf' m (Let _ expr) = typeOf' m expr
    typeOf' m (Case _ _ (a:_)) = typeOf' m a
    typeOf' m (Case _ _ _) = (TyBottom, m)
    typeOf' m (Type ty) = (ty, m)
    typeOf' m (Cast _ (_ :~ t')) = (t', m)
    typeOf' m (Coercion (_ :~ t')) = (t', m)
    typeOf' m (Assert _ _ e) = typeOf' m e
    typeOf' m (Assume _ e) = typeOf' m e

instance Typed Type where
    typeOf' m v@(TyVar (Id n _)) =
        case M.lookup n m of
            Just t -> (t, m)
            Nothing -> (v, m)
    -- typeOf' m (TyFun (TyForAll (NamedTyBndr i) t') t'') =
    --     let
    --         m' = M.insert (idName i) t'' m
    --     in
    --     typeOf' m' t'
    typeOf' m (TyFun t1 t2) =
        let
            (t1', m') = typeOf' m t1
            (t2', m'') = typeOf' m' t2
        in
        (TyFun t1' t2', m'')
    typeOf' m (TyApp t1 t2) =
        let
            (t1', m') = typeOf' m t1
            (t2', m'') = typeOf' m' t2
        in
        (mkTyApp t1' t2', m'')
        -- case t1' of
        --     TyConApp n _ -> (TyConApp n [t2'], m'')
        --     TyFun _ t2'' -> (t2'', m'')
        --     _ -> (TyApp t1' t2', m'')
    typeOf' m (TyConApp n ts) = (TyConApp n (map (fst . typeOf' m) ts), m)
    typeOf' m (TyForAll b t) = 
        let
            (t', m') = typeOf' m t
        in
        (TyForAll b t', m')
    typeOf' m t = (t, m)

newtype PresType = PresType Type

instance Typed PresType where
    typeOf' m (PresType t) = (t, m)

-- | Retyping
-- We look to see if the type we potentially replace has a TyVar whose Id is a
-- match on the target key that we want to replace.
retype :: (ASTContainer m Type, Show m) => Id -> Type -> m -> m
retype key new e = modifyContainedASTs (typeOf . retype' key new) $ e

retype' :: Id -> Type -> Type -> Type
retype' key new (TyVar test) = if key == test then new else TyVar test
retype' key new (TyForAll (NamedTyBndr nid) ty) =
  if key == nid
    then modifyChildren (retype' key new) ty
    else TyForAll (NamedTyBndr nid) (modifyChildren (retype' key new) ty)
retype' key new ty = modifyChildren (retype' key new) ty

-- | (.::)
-- Returns if the first type given is a specialization of the second,
-- i.e. if given t1, t2, returns true iff t1 :: t2
(.::) :: Typed t => t -> Type -> Bool
t1 .:: t2 = fst $ specializes M.empty (typeOf t1) t2

(.::.) :: Type -> Type -> Bool
t1 .::. t2 = fst (specializes M.empty t1 t2) && fst (specializes M.empty t2 t1)

specializes :: M.Map Name Type -> Type -> Type -> (Bool, M.Map Name Type)
specializes m _ TYPE = (True, m)
specializes m t (TyVar (Id n _)) =
    case M.lookup n m of
        Just (TyVar _) -> (True, m)
        Just t' -> specializes m t t'
        Nothing -> (True, M.insert n t m)
specializes m (TyFun t1 t2) (TyFun t1' t2') =
    let
        (b1, m') = specializes m t1 t1'
        (b2, m'') = specializes m' t2 t2'
    in
    (b1 && b2, m'')
specializes m (TyApp t1 t2) (TyApp t1' t2') =
    let
        (b1, m') = specializes m t1 t1'
        (b2, m'') = specializes m' t2 t2'
    in
    (b1 && b2, m'')
specializes m (TyConApp n ts) (TyConApp n' ts') =
    foldr 
        (\(t, t') (b, m') ->
            let 
                (b', m'') = specializes m' t t'
            in
            (b && b', m''))
        (n == n' && length ts == length ts', m) 
        (zip ts ts')
specializes m (TyConApp n ts) app@(TyApp _ _) =
    let
        appts = unTyApp app
    in
    case appts of
        TyConApp n' ts':ts'' -> specializes m (TyConApp n ts) (TyConApp n' $ ts' ++ ts'')
        _ -> (False, m)
specializes m app@(TyApp _ _) (TyConApp n ts) =
    let
        appts = unTyApp app
    in
    case appts of
        TyConApp n' ts':ts'' -> specializes m (TyConApp n ts) (TyConApp n' $ ts' ++ ts'')
        _ -> (False, m)

specializes m (TyFun t1 t2) (TyForAll (AnonTyBndr t1') t2') =
  let
      (b1, m') = specializes m t1 t1'
      (b2, m'') = specializes m' t2 t2'
  in (b1 && b2, m'')
specializes m (TyFun t1 t2) (TyForAll (NamedTyBndr _) t2') =
  specializes m (TyFun t1 t2) t2'
specializes m (TyForAll (AnonTyBndr t1) t2) (TyFun t1' t2') =
  let
      (b1, m') = specializes m t1 t1'
      (b2, m'') = specializes m' t2 t2'
  in (b1 && b2, m'')
specializes m (TyForAll (AnonTyBndr t1) t2) (TyForAll (AnonTyBndr t1') t2') =
  let
      (b1, m') = specializes m t1 t1'
      (b2, m'') = specializes m' t2 t2'
  in (b1 && b2, m'')
specializes m (TyForAll (AnonTyBndr t1) t2) (TyForAll (NamedTyBndr _) t2') =
  specializes m (TyForAll (AnonTyBndr t1) t2) t2'
specializes m (TyForAll (NamedTyBndr (Id _ t1)) t2) (TyForAll (NamedTyBndr (Id _ t1')) t2') =
  let
      (b1, m') = specializes m t1 t1'
      (b2, m'') = specializes m' t2 t2'
  in (b1 && b2, m'')
specializes m t (TyForAll _ t') = -- trace "SEVEN"
  specializes m t t'
specializes m TyUnknown _ = (True, m)
specializes m _ TyUnknown = (True, m)
specializes m TyBottom _ = (True, m)
specializes m _ TyBottom = (False, m)
specializes m t1 t2 = (t1 == t2, m)

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

-- | isAlgDataTy
isAlgDataTy :: Typed t => t -> Bool
isAlgDataTy = isAlgDataTy' . typeOf

isAlgDataTy' :: Type -> Bool
isAlgDataTy' (TyConApp _ _) = True
isAlgDataTy' _ = False

isTYPE :: Type -> Bool
isTYPE TYPE = True
isTYPE (TyConApp (Name "TYPE" _ _) _) = True
isTYPE _ = False

hasTYPE :: Type -> Bool
hasTYPE TYPE = True
hasTYPE (TyConApp (Name "TYPE" _ _) _) = True
hasTYPE (TyFun t t') = hasTYPE t || hasTYPE t'
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

-- tyVars
-- Returns a list of all tyVars
tyVars :: ASTContainer m Type => m -> [Type]
tyVars = evalASTs tyVars'

tyVars' :: Type -> [Type]
tyVars' t@(TyVar _) = [t]
tyVars' _ = []

-- hasTyBottom
hasTyBottom :: ASTContainer m Type => m -> Bool
hasTyBottom = getAny . evalASTs hasTyBottom'

hasTyBottom' :: Type -> Any
hasTyBottom' TyBottom = Any True
hasTyBottom' _ = Any False


-- | numArgs
numArgs :: Typed t => t -> Int
numArgs = length . argumentTypes

-- | argumentTypes
-- Gives the types of the arguments of the functions
data ArgType = JustType Type | BindType Id

argumentTypes :: Typed t => t -> [Type]
argumentTypes = argumentTypes' . typeOf

argumentTypes' :: Type -> [Type]
argumentTypes' (TyForAll (AnonTyBndr t1) t2) = t1:argumentTypes' t2
argumentTypes' (TyForAll (NamedTyBndr _) t2) = TYPE:argumentTypes' t2
argumentTypes' (TyFun t1 t2) = t1:argumentTypes' t2
argumentTypes' _ = []

spArgumentTypes :: Typed t => t -> [ArgType]
spArgumentTypes = spArgumentTypes' . typeOf

spArgumentTypes' :: Type -> [ArgType]
spArgumentTypes' (TyForAll (AnonTyBndr t1) t2) = JustType t1:spArgumentTypes' t2
spArgumentTypes' (TyForAll (NamedTyBndr i) t2) = BindType i:spArgumentTypes' t2
spArgumentTypes' (TyFun t1 t2) = JustType t1:spArgumentTypes' t2
spArgumentTypes' _ = []

tyForAllBindings :: Typed t => t -> [Id]
tyForAllBindings = tyForAllBindings' . typeOf

tyForAllBindings' :: Type -> [Id]
tyForAllBindings' (TyForAll (NamedTyBndr i) t) = i:tyForAllBindings' t
tyForAllBindings' (TyForAll _ t) = tyForAllBindings' t
tyForAllBindings' (TyFun t t') = tyForAllBindings' t ++ tyForAllBindings t'
tyForAllBindings' _ = []

nonTyForAllArgumentTypes :: Typed t => t -> [Type]
nonTyForAllArgumentTypes = nonTyForAllArgumentTypes' . typeOf

nonTyForAllArgumentTypes' :: Type -> [Type]
nonTyForAllArgumentTypes' (TyForAll _ t) = nonTyForAllArgumentTypes t
nonTyForAllArgumentTypes' (TyFun t1 t2) = t1:nonTyForAllArgumentTypes' t2
nonTyForAllArgumentTypes' _ = []

-- | returnType
-- Gives the return type if the given function type is fully saturated
returnType :: Typed t => t -> Type
returnType = returnType' . typeOf

returnType' :: Type -> Type
returnType' (TyForAll _ t) = returnType' t
returnType' (TyFun _ t) = returnType' t
returnType' t = t

-- | polyIds
-- Returns all polymorphic Ids in the given type
polyIds :: Type -> [Id]
polyIds = fst . splitTyForAlls

-- | splitTyForAlls
-- Turns TyForAll types into a list of type ids
splitTyForAlls :: Type -> ([Id], Type)
splitTyForAlls (TyForAll (NamedTyBndr i) t) =
    let
        (i', t') = splitTyForAlls t
    in
    (i:i', t')
splitTyForAlls t = ([], t)


-- Turns TyFun types into a list of types
splitTyFuns :: Type -> [Type]
splitTyFuns (TyFun t t') = t:splitTyFuns t'
splitTyFuns t = [t]

-- | tyForAlls
-- Nests a new type in TyForAlls
nestTyForAlls :: Type -> (Type -> Type)
nestTyForAlls (TyForAll b t) = TyForAll b . nestTyForAlls t
nestTyForAlls _ = id

inTyForAlls :: Type -> Type
inTyForAlls (TyForAll _ t) = inTyForAlls t
inTyForAlls t = t

-- TODO: Seems not ideal?  Why do we have 2 ways to represent this?  What is:
collapseTyConApp :: Type -> Type
collapseTyConApp = modifyFix collapseTyConApp'

collapseTyConApp' :: Type -> Type
collapseTyConApp' tyf@(TyFun (TyConApp n ts) t)
    | getAny $ evalASTs (Any . isTyVar) ts = TyConApp n $ replaceFstTyVar ts t
    | otherwise = tyf
collapseTyConApp' t = t

replaceFstTyVar :: [Type] -> Type -> [Type]
replaceFstTyVar (TyVar _:ts) t' = t':ts
replaceFstTyVar (tca@(TyConApp n ts):ts') t' =
    let
        rtca = replaceFstTyVar ts t'
    in
    if ts == rtca 
        then tca:replaceFstTyVar ts' t'
        else TyConApp n rtca:ts'
replaceFstTyVar (t:ts) t' = t:replaceFstTyVar ts t'
replaceFstTyVar [] _ = []
    -- case break isTyVar ts of
    --     (b, a:as) -> b ++ t:as
    --     _ -> ts
