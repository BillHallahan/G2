-- | Type Checker
--   Provides type checking capabilities over G2 Language.
module G2.Internals.Language.Typing
    ( Typed (..)
    , (.::)
    , hasFuncType
    , returnType
    , splitTyForAlls
    , splitTyFuns
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Syntax

import qualified Data.Map as M
import qualified Data.Set as S

-- | Typed typeclass.
class Typed a where
    typeOf :: a -> Type
    typeOf = typeOf' M.empty

    typeOf' :: M.Map Name Type -> a -> Type

    retype :: Type -> Type -> a -> a


-- | `Id` instance of `Typed`.
instance Typed Id where
    typeOf' m (Id _ ty) = typeOf' m ty

    retype old new (Id name ty) = Id name (retype old new ty)

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

    retype _ _ prim = prim

-- | `Lit` instance of `Typed`.
instance Typed Lit where
    typeOf (LitInt _) = TyLitInt
    typeOf (LitFloat _) = TyLitFloat
    typeOf (LitDouble _) = TyLitDouble
    typeOf (LitChar _)   = TyLitChar
    typeOf (LitString _) = TyLitString
    typeOf (LitBool _) = TyBool

    typeOf' _ = typeOf

    retype _ _ lit = lit

-- | `DataCon` instance of `Typed`.
instance Typed DataCon where
    typeOf' _ (DataCon _ ty _) = ty
    typeOf' _ (PrimCon I) = TyFun TyLitInt TyInt
    typeOf' _ (PrimCon D) = TyFun TyLitDouble TyDouble
    typeOf' _ (PrimCon F) = TyFun TyLitFloat TyFloat
    typeOf' _ (PrimCon C) = TyFun TyLitChar TyChar
    typeOf' _ (PrimCon B) = TyBool

    retype old new (DataCon name ty tys) =
      DataCon name (retype old new ty) (map (retype old new) tys)
    retype _ _ primcon = primcon

-- | `Alt` instance of `Typed`.
instance Typed Alt where
    typeOf' m (Alt _ expr) = typeOf' m expr

    retype old new (Alt am expr) = Alt am' (retype old new expr)
      where
        am' = case am of
          DataAlt dcon ids -> DataAlt (retype old new dcon)
                                      (map (retype old new) ids)
          _ -> am

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

    retype old new = modifyASTs go
      where
        go :: Expr -> Expr
        go (Var i) = Var (retype old new i)
        go (Prim p ty) = Prim (retype old new p) (retype old new ty)
        go (Data d) = Data (retype old new d)
        go (App fe ae) = App (retype old new fe) (retype old new ae)
        go (Lam i e) = Lam (retype old new i) (retype old new e)
        go (Let b e) =
          let b' = map (\(n, r) -> (retype old new n, retype old new r)) b
          in Let b' (retype old new e)
        go (Case e i a) =
          Case (retype old new e) (retype old new i) (map (retype old new) a)
        go (Type t) = Type (retype old new t)
        go e = e

instance Typed Type where
    typeOf = typeOf' M.empty

    typeOf' m v@(TyVar n _) =
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

    retype old new test =
      if old == test then new else case test of
        TyVar n t -> if old == t then new else TyVar n (retype old new t)
        TyFun t1 t2 -> TyFun (retype old new t1) (retype old new t2)
        TyApp t1 t2 -> TyApp (retype old new t1) (retype old new t2)
        TyConApp n ts -> TyConApp n (map (retype old new) ts)
        TyForAll (AnonTyBndr bt) ty ->
          TyForAll (AnonTyBndr (retype old new bt)) (retype old new ty)
        TyForAll (NamedTyBndr n) ty ->
          TyForAll (NamedTyBndr (retype old new n)) (retype old new ty)
        ty -> if old == ty then new else ty

-- | Returns if the first type given is a specialization of the second,
-- i.e. if given t1, t2, returns true iff t1 :: t2
-- TODO: FIX THIS FUNCTION
(.::) :: Typed t => t -> Type -> Bool
(.::) t1 t2 = specializesTo M.empty S.empty (typeOf t1) t2

specializesTo :: M.Map Name Type -> S.Set Type -> Type -> Type -> Bool
specializesTo m s t (TyVar n t') =
    if S.member t' s
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
    specializesTo (M.insert n t1 m) (S.insert t1' s) (TyFun t1 t2) t2'
-- Forall / forall bindings.
specializesTo m s (TyForAll (AnonTyBndr t1) t2) (TyForAll (AnonTyBndr t1') t2') =
    specializesTo m s t1 t1' && specializesTo m s t2 t2'
specializesTo m s (TyForAll (NamedTyBndr (Id _ t1)) t2)
                (TyForAll (NamedTyBndr (Id n' t1')) t2') =
    specializesTo (M.insert n' t1 m) (S.insert t1' s) t2 t2'
-- The rest.
specializesTo _ _ TyBottom _ = True
specializesTo _ _ _ TyBottom = True
specializesTo _ s t t' = S.member t' s || t == t'

hasFuncType :: (Typed t) => t -> Bool
hasFuncType t =
    case typeOf t of
        (TyFun _ _) -> True
        (TyForAll _ _)  -> True
        _ -> False

returnType :: (Typed t) => t -> Type
returnType = returnType' . typeOf

returnType' :: Type -> Type
returnType' (TyForAll _ t) = returnType' t
returnType' (TyFun _ t) = returnType' t
returnType' t = t

-- | Turns TyForAll types into a list of types
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
