{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- | Type Checker
--   Provides type checking capabilities over G2 Language.
module G2.Internals.Language.Typing
    ( Typed (..)
    , (.::)
    , hasFuncType
    , appendType
    , higherOrderFuncs
    , isPolyFunc
    , returnType
    , polyIds
    , splitTyForAlls
    , splitTyFuns
    , retype
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Syntax

import qualified Data.Map as M
import qualified Data.HashSet as HS

-- | Typed typeclass.
class Typed a where
    typeOf :: a -> Type
    typeOf = typeOf' M.empty

    typeOf' :: M.Map Name Type -> a -> Type

-- | `Id` instance of `Typed`.
instance Typed Id where
    typeOf' m (Id _ ty) = typeOf' m ty

-- | `Primitive` instance of `Typed`
instance Typed Primitive where
    typeOf Ge = TyBottom  -- TODO: fill in correctly.
    typeOf Gt = TyBottom
    typeOf Eq = TyBottom
    typeOf Lt = TyBottom
    typeOf Le = TyBottom
    typeOf Neq = TyBottom
    typeOf And = TyFun TyBool (TyFun TyBool TyBool)
    typeOf Or = TyFun TyBool (TyFun TyBool TyBool)
    typeOf Not = TyFun TyBool TyBool
    typeOf Implies = TyFun TyBool (TyFun TyBool TyBool)
    typeOf Plus = TyBottom
    typeOf Minus = TyBottom
    typeOf Mult = TyBottom
    typeOf Div = TyBottom
    typeOf Negate = TyBottom
    typeOf Error = TyBottom
    typeOf Undefined = TyBottom

    typeOf' _ = typeOf

-- | `Lit` instance of `Typed`.
instance Typed Lit where
    typeOf (LitInt _) = TyLitInt
    typeOf (LitFloat _) = TyLitFloat
    typeOf (LitDouble _) = TyLitDouble
    typeOf (LitChar _)   = TyLitChar
    typeOf (LitString _) = TyLitString
    typeOf (LitBool _) = TyBool

    typeOf' _ = typeOf

-- | `DataCon` instance of `Typed`.
instance Typed DataCon where
    typeOf' _ (DataCon _ ty _) = ty
    typeOf' _ (PrimCon I) = TyFun TyLitInt TyInt
    typeOf' _ (PrimCon D) = TyFun TyLitDouble TyDouble
    typeOf' _ (PrimCon F) = TyFun TyLitFloat TyFloat
    typeOf' _ (PrimCon C) = TyFun TyLitChar TyChar
    typeOf' _ (PrimCon B) = TyBool

-- | `Alt` instance of `Typed`.
instance Typed Alt where
    typeOf' m (Alt _ expr) = typeOf' m expr

-- | `Expr` instance of `Typed`.
instance Typed Expr where
    typeOf' m (Var v) = typeOf' m v
    typeOf' m (Lit lit) = typeOf' m lit
    typeOf' _ (Prim _ ty) = ty
    typeOf' m (Data dcon) = typeOf' m dcon
    typeOf' m (App fxpr axpr) =
        let
            tfxpr = typeOf' m fxpr
            taxpr = typeOf' m axpr
        in
        case tfxpr of
            TyForAll (NamedTyBndr i) t2 -> typeOf' (M.insert (idName i) taxpr m) t2
            TyFun _ t2 ->  t2  -- if t1 == tfxpr then t2 else TyBottom -- TODO:
                               -- We should really have this if check- but
                               -- can't because of TyBottom being introdduced
                               -- elsewhere...
            _ -> TyBottom
    typeOf' m (Lam b expr) = TyFun (typeOf' m b) (typeOf' m expr)
    typeOf' m (Let _ expr) = typeOf' m expr
    typeOf' m (Case _ _ (a:_)) = typeOf' m a
    typeOf' _ (Case _ _ _) = TyBottom
    typeOf' _ (Type ty) = ty
    typeOf' m (Assert _ e) = typeOf' m e
    typeOf' m (Assume _ e) = typeOf' m e

instance Typed Type where
    typeOf = typeOf' M.empty

    typeOf' m v@(TyVar (Id n _)) =
        case M.lookup n m of
            Just t -> t
            Nothing -> v
    typeOf' m (TyFun (TyForAll (NamedTyBndr i) t') t'') =
        let
            m' = M.insert (idName i) t'' m
        in
        typeOf' m' t'
    typeOf' m (TyFun t t') = TyFun (typeOf' m t) (typeOf' m t')
    typeOf' _ t = t

-- | Retyping
-- We look to see if the type we potentially replace has a TyVar whose Id is a
-- match on the target key that we want to replace.
retype :: ASTContainer m Type => Id -> Type -> m -> m
retype key new = modifyContainedASTs (retype' key new)

retype' :: Id -> Type -> Type -> Type
retype' key new (TyVar test) = if key == test then new else TyVar test
retype' key new ty = modifyChildren (retype key new) ty

-- | (.::)
-- Returns if the first type given is a specialization of the second,
-- i.e. if given t1, t2, returns true iff t1 :: t2
(.::) :: Typed t => t -> Type -> Bool
(.::) t1 t2 = specializesTo M.empty HS.empty (typeOf t1) t2

specializesTo :: M.Map Name Type -> HS.HashSet Type -> Type -> Type -> Bool
specializesTo m s t (TyVar (Id n t')) =
    if HS.member t' s
        then case M.lookup n m of
            Just r -> specializesTo m s t r  -- There is an entry.
            Nothing -> True  -- We matched with TOP, oh well.
        else specializesTo m s t t'  -- Not a TOP.
-- Apply direct AST recursion.
specializesTo m s (TyFun t1 t2) (TyFun t1' t2') =
    specializesTo m s t1 t1' && specializesTo m s t2 t2'
specializesTo m s (TyApp t1 t2) (TyApp t1' t2') =
    specializesTo m s t1 t1' && specializesTo m s t2 t2'
specializesTo m s (TyConApp _ ts) (TyConApp _ ts') =
    length ts == length ts' &&
    all (\(t, t') -> specializesTo m s t t') (zip ts ts')
-- Unhandled function type.
specializesTo m s (TyFun t1 t2) (TyForAll (AnonTyBndr t1') t2') =
    specializesTo m s t1 t1' && specializesTo m s t2 t2'
-- For all function type bindings.
specializesTo m s (TyFun t1 t2) (TyForAll (NamedTyBndr (Id n t1')) t2') =
    specializesTo (M.insert n t1 m) (HS.insert t1' s) (TyFun t1 t2) t2'
-- Forall / forall bindings.
specializesTo m s (TyForAll (AnonTyBndr t1) t2) (TyForAll (AnonTyBndr t1') t2') =
    specializesTo m s t1 t1' && specializesTo m s t2 t2'
specializesTo m s (TyForAll (NamedTyBndr (Id _ t1)) t2)
                (TyForAll (NamedTyBndr (Id n' t1')) t2') =
    specializesTo (M.insert n' t1 m) (HS.insert t1' s) t2 t2'
-- The rest.
specializesTo _ _ TyBottom _ = True
specializesTo _ _ _ TyBottom = True
specializesTo _ s t t' = HS.member t' s || t == t'

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

-- | isPolyFunc
-- Checks if the given function is a polymorphic function
isPolyFunc ::  Typed t => t -> Bool
isPolyFunc = isPolyFunc' . typeOf

isPolyFunc' :: Type -> Bool
isPolyFunc' (TyForAll _ _) = True
isPolyFunc' _ = False

-- | returnType
-- Gives the return type if the given function type is fully saturated
returnType :: (Typed t) => t -> Type
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

-- | splitTyFuns
-- Turns TyFun types into a list of types
splitTyFuns :: Type -> [Type]
splitTyFuns (TyFun t t') = t:splitTyFuns t'
splitTyFuns t = [t]
