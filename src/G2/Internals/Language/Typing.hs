-- | Type Checker
--   Provides type checking capabilities over G2 Language.
module G2.Internals.Language.Typing
    ( Typed (..)
    , (.::)
    , splitTyForAlls
    , splitTyFuns
    ) where

import G2.Internals.Language.Syntax

import qualified Data.Map as M

-- | Typed typeclass.
class Typed a where
    typeOf :: a -> Type


-- | `Id` instance of `Typed`.
instance Typed Id where
    typeOf (Id _ ty) = ty

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
    typeOf UNeg = TyBottom

-- | `Lit` instance of `Typed`.
instance Typed Lit where
    typeOf (LitInt _) = TyLitInt
    typeOf (LitFloat _) = TyLitFloat
    typeOf (LitDouble _) = TyLitDouble
    typeOf (LitChar _)   = TyLitChar
    typeOf (LitString _) = TyLitString
    typeOf (LitBool _) = TyBool

-- | `DataCon` instance of `Typed`.
instance Typed DataCon where
    typeOf (DataCon _ ty tys) = foldr TyFun ty tys
    typeOf (PrimCon I) = TyFun TyLitInt TyInt
    typeOf (PrimCon D) = TyFun TyLitDouble TyDouble
    typeOf (PrimCon F) = TyFun TyLitFloat TyFloat
    typeOf (PrimCon C) = TyFun TyLitChar TyChar
    typeOf (PrimCon B) = TyBool

-- | `Alt` instance of `Typed`.
instance Typed Alt where
    typeOf (Alt _ expr) = typeOf expr

-- | `Expr` instance of `Typed`.
instance Typed Expr where
    typeOf (Var v) = typeOf v
    typeOf (Lit lit) = typeOf lit
    typeOf (Prim prim ty) = ty
    typeOf (Data dcon) = typeOf dcon
    typeOf (App fxpr axpr) =
        let
            tfxpr = typeOf fxpr
            taxpr = typeOf axpr
        in
        case tfxpr of
            TyForAll _ t2 -> t2
            TyFun t1 t2 -> t2 -- if t1 == tfxpr then t2 else TyBottom -- TODO: We should really have this if check- but can't because of TyBottom being introdduced elsewhere...
            _ -> TyBottom
    typeOf (Lam b expr) = TyFun (typeOf b) (typeOf expr)
    typeOf (Let _ expr) = typeOf expr
    typeOf (Case _ _ (a:_)) = typeOf a
    typeOf (Type ty) = ty
    typeOf (Assert _ e) = typeOf e
    typeOf (Assume _ e) = typeOf e


-- | Returns if the first type given is a specialization of the second,
-- i.e. if given t1, t2, returns true iff t1 :: t2
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