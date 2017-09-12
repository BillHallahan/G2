-- | Type Checker
--   Provides type checking capabilities over G2 Language.
module G2.Internals.Language.Typing
    ( Typed (..)
    , (.::)
    , returnType
    , splitTyForAlls
    , splitTyFuns
    ) where

import G2.Internals.Language.Syntax

import qualified Data.Map as M

-- | Typed typeclass.
class Typed a where
    typeOf :: a -> Type
    typeOf' :: M.Map Name Type -> a -> Type

    typeOf = typeOf' M.empty


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
    typeOf' m (DataCon _ ty tys) = foldr TyFun (typeOf' m ty) tys
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
    typeOf' m (Prim prim ty) = ty
    typeOf' m (Data dcon) = typeOf' m dcon
    typeOf' m (App fxpr axpr) =
        let
            tfxpr = typeOf' m fxpr
            taxpr = typeOf' m axpr
        in
        case tfxpr of
            TyForAll (NamedTyBndr i) t2 -> typeOf' (M.insert (idName i) taxpr m) t2
            TyFun t1 t2 ->  t2 -- if t1 == tfxpr then t2 else TyBottom -- TODO: We should really have this if check- but can't because of TyBottom being introdduced elsewhere...
            _ -> TyBottom
    typeOf' m (Lam b expr) = TyFun (typeOf' m b) (typeOf' m expr)
    typeOf' m (Let _ expr) = typeOf' m expr
    typeOf' m (Case _ _ (a:_)) = typeOf' m a
    typeOf' m (Type ty) = ty
    typeOf' m (Assert _ e) = typeOf' m e
    typeOf' m (Assume _ e) = typeOf' m e

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

-- | Returns if the first type given is a specialization of the second,
-- i.e. if given t1, t2, returns true iff t1 :: t2
-- TODO: FIX THIS FUNCTION
(.::) :: Typed t => t -> t -> Bool
(.::) t1 t2 = specializesTo M.empty (typeOf t1) (typeOf t2)

specializesTo :: M.Map Name Type -> Type -> Type -> Bool
specializesTo m (TyVar n t) (TyVar n' t') = specializesTo m t t'
specializesTo m (TyFun t1 t2) (TyFun t1' t2') =
    specializesTo m t1 t1' && specializesTo m t2 t2'
specializesTo m (TyApp t1 t2) (TyApp t1' t2') =
    specializesTo m t1 t1' && specializesTo m t2 t2'
specializesTo m (TyConApp n ts) (TyConApp n' ts') =
    length ts == length ts' 
    && all (\(t, t') -> specializesTo m t t') (zip ts ts')
specializesTo m (TyForAll b t) (TyForAll b' t') = specializesTo m t t'
specializesTo _ t t' = t == t'

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
