-- | Defines typeclasses and functions for ease of AST manipulation.

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.AST
    ( module G2.Internals.Language.AST
    ) where

import G2.Internals.Language.Syntax

import Data.Hashable
import qualified Data.HashSet as HS

-- | Describes the data types that can be represented in a tree format.
class AST t where
    -- | Gets the direct children of the given node.
    children :: t -> [t]
    -- | Applies the given function to all children of the given node.
    modifyChildren :: (t -> t) -> t -> t

-- | Calls the given function on the given node, and all of the descendants
-- in a recursive manner.
modify :: AST t => (t -> t) -> t -> t
modify f t = modifyChildren (modify f) (f t)

-- | Similar to modify. Also passes a Monoid instance to the modify function. 
-- Children have access to the mconcated results from higher in the tree
-- As exposed by modifyM, the head of the tree is given mempty.
modifyM :: (AST t, Monoid a) => (a -> t -> (t, a)) -> t -> t
modifyM f = go f mempty
  where
    go :: (AST t, Monoid a) => (a -> t -> (t, a)) -> a -> t -> t
    go g m t = let (t', m') = g m t
                   ms = m `mappend` m'
               in modifyChildren (go g ms) t'

-- | Runs the given function f on the node t, t until t = f t, then does the
-- same on all decendants of t recursively.
modifyFix :: (AST t, Eq t) => (t -> t) -> t -> t
modifyFix f t = let t' = f t
                in if t == t'
                    then modifyChildren (modifyFix f) t'
                    else modifyFix f t'

-- | Combines the methods of modifyM and modifyFix.
-- Runs until t == t', but does not consider the Monoid's value. However, the
-- mappend still occurs each time an iteration is performed on a given AST.
modifyFixM :: (AST t, Eq t, Monoid a) => (a -> t -> (t, a)) -> t -> t
modifyFixM f = go f mempty
  where
    go :: (AST t, Eq t, Monoid a) => (a -> t -> (t, a)) -> a -> t -> t
    go g m t =  let (t', m') = g m t
                    ms = m `mappend` m'
                in if t == t'
                    then modifyChildren (go g ms) t'
                    else go g ms t'

-- | Recursively runs the given function on each node, top down. Uses mappend
-- to combine the results after evaluation of the entire tree.
eval :: (AST t, Monoid a) => (t -> a) -> t -> a
eval f t = (f t) `mappend` (evalChildren (eval f) t)

evalM :: (AST t, Monoid a, Monoid b) => (b -> t -> (b, a)) -> t -> a
evalM f = go f mempty
    where
        go :: (AST t, Monoid a, Monoid b) => (b -> t -> (b, a)) -> b -> t -> a
        go g b t = let
                        (b', a') = g b t
                        b'' = b `mappend` b'
                   in
                   a' `mappend` evalChildren (go g b'') t

-- | Evaluation of Children
evalChildren :: (AST t, Monoid a) => (t -> a) -> t -> a
evalChildren f = mconcat . (map f) . children

-- | For types that contain ASTs, but that are not ASTs themselves. Such types
-- may include environments, state, and the like.
class AST t => ASTContainer c t where
    -- | Gets all the ASTs that are recursively contained in the container.
    containedASTs :: c -> [t]
    -- | Calls the function on all ASTs in the container.
    modifyContainedASTs :: (t -> t) -> c -> c

-- | Runs modify on all the ASTs in the container.
modifyASTs :: ASTContainer t e => (e -> e) -> t -> t
modifyASTs f = modifyContainedASTs (modify f)

-- | Runs modifyM on all the ASTs in the container.
modifyASTsM :: (ASTContainer t e, Monoid a) => (a -> e -> (e,a)) -> t -> t
modifyASTsM f = modifyContainedASTs (modifyM f)

-- | Runs modifyFix on all the ASTs in the container.
modifyASTsFix :: (ASTContainer t e, Eq e) => (e -> e) -> t -> t
modifyASTsFix f = modifyContainedASTs (modifyFix f)

-- | Runs eval on all the ASTs in the container, and uses mappend to results.
evalASTs :: (ASTContainer t e, Monoid a) => (e -> a) -> t -> a
evalASTs f = evalContainedASTs (eval f)

evalASTsM :: (ASTContainer t e, Monoid a, Monoid b) => (b -> e -> (b, a)) -> t -> a
evalASTsM f = evalContainedASTs (evalM f)

-- | Runs a function on all the ASTs in the container, and uses mappend to
-- combine the results.
evalContainedASTs :: (ASTContainer t e, Monoid a) => (e -> a) -> t -> a
evalContainedASTs f = mconcat . map f . containedASTs

-- | Instance Expr of AST
instance AST Expr where
    children (Var _) = []
    children (Lit _) = []
    children (Prim _ _) = []
    children (Data _) = []
    children (App f a) = [f, a]
    children (Lam _ e) = [e]
    children (Let bind e) = e : containedASTs bind
    children (Case m _ as) = m : map (\(Alt _ e) -> e) as
    children (Type _) = []
    children (Assume e e') = [e, e']
    children (Assert e e') = [e, e']

    modifyChildren f (App fx ax) = App (f fx) (f ax)
    modifyChildren f (Lam b e) = Lam b (f e)
    modifyChildren f (Let bind e) = Let (modifyContainedASTs f bind) (f e)
    modifyChildren f (Case m b as) = Case (f m) b (mapAlt f as)
      where
        mapAlt :: (Expr -> Expr) -> [Alt] -> [Alt]
        mapAlt g alts = map (\(Alt ac e) -> Alt ac (g e)) alts
    modifyChildren f (Assume e e') = Assume (f e) (f e')
    modifyChildren f (Assert e e') = Assert (f e) (f e')
    modifyChildren _ e = e

instance AST Type where
    children (TyVar i) = containedASTs i
    children (TyFun tf ta) = [tf, ta]
    children (TyApp tf ta) = [tf, ta]
    children (TyConApp _ ts) = ts
    children (TyForAll b t)  = containedASTs b ++ [t]
    children _ = []

    modifyChildren f (TyVar i) = TyVar $ modifyContainedASTs f i
    modifyChildren f (TyFun tf ta)   = TyFun (f tf) (f ta)
    modifyChildren f (TyApp tf ta)   = TyApp (f tf) (f ta)
    modifyChildren f (TyConApp b ts) = TyConApp b (map f ts)
    modifyChildren f (TyForAll b t)  = TyForAll (modifyContainedASTs f b) (f t)
    modifyChildren _ t               = t

instance AST DataCon where
    children _ = []
    modifyChildren _ (DataCon n ty tys) = DataCon n ty tys
    modifyChildren _ (PrimCon pcon) = PrimCon pcon

-- | Instance ASTContainer of Itself
--   Every AST is defined as an ASTContainer of itself. Generally, functions
--   should be written using the ASTContainer typeclass.
instance AST t => ASTContainer t t where
    containedASTs t = [t]

    modifyContainedASTs f t = f t

instance ASTContainer Expr Type where
    containedASTs = eval go
      where
            go :: Expr -> [Type]
            go (Var i) = containedASTs i
            go (Prim _ t) = [t]
            go (Data dc) = containedASTs dc
            go (Lam b e) = containedASTs b ++ containedASTs e
            go (Let bnd e) = containedASTs bnd ++ containedASTs e
            go (Case e i as) = containedASTs e ++ containedASTs i ++ containedASTs as
            go (Type t) = [t]
            go (Assume e e') = containedASTs e ++ containedASTs e'
            go (Assert e e') = containedASTs e ++ containedASTs e'
            go _ = []

    modifyContainedASTs f = modify go
      where
            go :: Expr -> Expr
            go (Var i) = Var (modifyContainedASTs f i)
            go (Prim p t) = Prim p (modifyContainedASTs f t)
            go (Data dc) = Data (modifyContainedASTs f dc)
            go (App fx ax) = App (modifyContainedASTs f fx) (modifyContainedASTs f ax)
            go (Lam b e) = Lam (modifyContainedASTs f b) (modifyContainedASTs f e)
            go (Let bnd e) = Let (modifyContainedASTs f bnd) (modifyContainedASTs f e)
            go (Case m i as) = Case (modifyContainedASTs f m) (modifyContainedASTs f i) (modifyContainedASTs f as) 
            go (Type t) = Type (f t)
            go (Assume e e') = Assume (modifyContainedASTs f e) (modifyContainedASTs f e')
            go (Assert e e') = Assert (modifyContainedASTs f e) (modifyContainedASTs f e')
            go e = e

instance ASTContainer Id Expr where
  containedASTs (Id _ _) = []

  modifyContainedASTs _ i = i

instance ASTContainer Id Type where
  containedASTs (Id _ t) = [t]

  modifyContainedASTs f (Id n t) = Id n (modifyContainedASTs f t)

instance ASTContainer Name Expr where
    containedASTs _ = []
    modifyContainedASTs _ n = n

instance ASTContainer Name Type where
    containedASTs _ = []
    modifyContainedASTs _ n = n
  
instance ASTContainer Type Expr where
    containedASTs _ = []
    modifyContainedASTs _ t = t

instance ASTContainer DataCon Expr where
    containedASTs _ = []
    modifyContainedASTs _ d = d

instance ASTContainer DataCon Type where
    containedASTs (DataCon _ t ts) = containedASTs (t:ts)
    containedASTs _ = []

    modifyContainedASTs f (DataCon n t ts) = DataCon n (f t) (map f ts)
    modifyContainedASTs _ (PrimCon pcon) = PrimCon pcon

instance ASTContainer AltMatch Expr where
    containedASTs _ = []
    modifyContainedASTs _ e = e

instance ASTContainer AltMatch Type where
    containedASTs (DataAlt dc i) = containedASTs dc ++ containedASTs i
    containedASTs _ = []

    modifyContainedASTs f (DataAlt dc i) = DataAlt (modifyContainedASTs f dc) (modifyContainedASTs f i)
    modifyContainedASTs _ e = e

instance ASTContainer Alt Expr where
    containedASTs (Alt _ e) = [e]
    modifyContainedASTs f (Alt a e) = Alt a (f e)

instance ASTContainer Alt Type where
    containedASTs (Alt a e) = (containedASTs a) ++ (containedASTs e)
    modifyContainedASTs f (Alt a e) =
        Alt (modifyContainedASTs f a) (modifyContainedASTs f e)

instance ASTContainer TyBinder Expr where
    containedASTs _ = []
    modifyContainedASTs _ b = b

instance ASTContainer TyBinder Type where
    containedASTs (AnonTyBndr t) = [t]
    containedASTs (NamedTyBndr i) = containedASTs i

    modifyContainedASTs f (AnonTyBndr t) = AnonTyBndr (f t)
    modifyContainedASTs f (NamedTyBndr i) = NamedTyBndr (modifyContainedASTs f i)

instance {-# OVERLAPPING #-} (Foldable f, Functor f, ASTContainer c t) => ASTContainer (f c) t where
    containedASTs = foldMap (containedASTs)

    modifyContainedASTs f = fmap (modifyContainedASTs f)

instance {-# OVERLAPPING #-} (ASTContainer s t, Hashable s, Eq s) => ASTContainer (HS.HashSet s) t where
    containedASTs = containedASTs . HS.toList 

    modifyContainedASTs f = HS.map (modifyContainedASTs f)

instance {-# OVERLAPPING #-} (ASTContainer c t, ASTContainer d t) => ASTContainer (c, d) t where
    containedASTs (x, y) = containedASTs x ++ containedASTs y

    modifyContainedASTs f (x, y) = (modifyContainedASTs f x, modifyContainedASTs f y)

instance {-# OVERLAPPING #-} 
    (ASTContainer c t, ASTContainer d t, ASTContainer e t) => ASTContainer (c, d, e) t where
        containedASTs (x, y, z) = containedASTs x ++ containedASTs y ++ containedASTs z

        modifyContainedASTs f (x, y, z) = (modifyContainedASTs f x, modifyContainedASTs f y, modifyContainedASTs f z)

instance {-# OVERLAPPING #-} 
    (ASTContainer c t, ASTContainer d t, ASTContainer e t, ASTContainer g t) => ASTContainer (c, d, e, g) t where
        containedASTs (x, y, z, w) = containedASTs x ++ containedASTs y ++ containedASTs z ++ containedASTs w

        modifyContainedASTs f (x, y, z, w) = (modifyContainedASTs f x, modifyContainedASTs f y, modifyContainedASTs f z, modifyContainedASTs f w)

-- | Miscellaneous Instances
--   These instances exist so that we can use them in other types that contain
--   ASTs and still consider those types ASTContainers. For example (Expr, Bool)
--   should be an ASTContainer.
instance ASTContainer Lit Expr where
    containedASTs _ = []
    modifyContainedASTs _ t = t

instance ASTContainer Lit Type where
    containedASTs _ = []
    modifyContainedASTs _ t = t

instance ASTContainer Bool Expr where
    containedASTs _ = []
    modifyContainedASTs _ t = t

instance ASTContainer Bool Type where
    containedASTs _ = []
    modifyContainedASTs _ t = t

instance ASTContainer Char Expr where
    containedASTs _ = []
    modifyContainedASTs _ t = t

instance ASTContainer Char Type where
    containedASTs _ = []
    modifyContainedASTs _ t = t

instance ASTContainer Int Expr where
    containedASTs _ = []
    modifyContainedASTs _ t = t

instance ASTContainer Int Type where
    containedASTs _ = []
    modifyContainedASTs _ t = t

-- ====== --
-- AST Helper functions
-- ====== --

-- | replaceASTs
-- Replaces all instances of old with new in the ASTContainer
replaceASTs :: (Eq e, ASTContainer c e) => e -> e -> c -> c
replaceASTs old new = modifyContainedASTs (replaceASTs' old new)

replaceASTs' :: (Eq e, AST e) => e -> e -> e -> e
replaceASTs' old new e = if e == old then new else modifyChildren (replaceASTs' old new) e
