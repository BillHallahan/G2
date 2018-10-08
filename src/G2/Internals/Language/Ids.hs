{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Language.Ids where

import G2.Internals.Language.Syntax
import G2.Internals.Language.AST

import qualified Data.Map as M
import qualified Data.HashSet as HS

class Ided a where
    ids :: a -> [Id]

instance Ided Id where
    ids i = [i]

instance Ided Name where
    ids _ = []

instance Ided Expr where
    ids = eval go
        where
            go :: Expr -> [Id]
            go (Var i) = [i]
            go (Prim _ t) = ids t
            go (Data d) = ids d
            go (Lam _ i _) = [i]
            go (Let b _) = concatMap (ids . fst) b
            go (Case _ i a) = i:concatMap (ids . altMatch) a
            go (Type t) = ids t
            go _ = []

instance Ided Type where
    ids = eval go
        where
            go (TyVar i) = [i]
            go (TyForAll b _) = ids b
            go _ = []

instance Ided DataCon where
    ids (DataCon _ t) = ids t

instance Ided AltMatch where
    ids (DataAlt dc i) = ids dc ++ i
    ids _ = []

instance Ided TyBinder where
    ids (AnonTyBndr t) = ids t
    ids (NamedTyBndr i) = [i]

instance Ided Coercion where
    ids (t1 :~ t2) = ids t1 ++ ids t2

instance Ided a => Ided [a] where
    ids = foldMap ids

instance Ided a => Ided (Maybe a) where
    ids = foldMap ids

instance Ided a => Ided (M.Map k a) where
    ids = foldMap ids

instance Ided s => Ided (HS.HashSet s) where
    ids = foldMap ids

instance (Ided a, Ided b) => Ided (a, b) where
    ids (a, b) = ids a ++ ids b

instance (Ided a, Ided b, Ided c) => Ided (a, b, c) where
    ids (a, b, c) = ids a ++ ids b ++ ids c
