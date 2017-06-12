-- | ASTHandler
--   This module provides two type classes and several higher order functions
--   to ease the handling of ASTs, in particular, Expr and Types.
--   See tests/UnitTests.hs for examples.

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Core.ASTHandler where

import qualified Data.Map as M

import G2.Internals.Core.Language

-- | Abstract Syntax Tree
--   Describes the data types that can be represented in a tree format.
class AST t where
    -- | Children
    --   Gets the direct children of the given node.
    children :: t -> [t]
    -- | Modify Children
    --   Applies the given function to all children of the given node.
    modifyChildren :: (t -> t) -> t -> t

-- | Modify
--   Calls the given function on the given node, and all of the descendants
--   in a recursive manner.
modify :: AST t => (t -> t) -> t -> t
modify f t = modifyChildren (modify f) (f t)

-- | Monoidic Modify
--   Similar to modify. Also passes a Monoid instance to the modify function. 
--   Children have access to the mconcated results from higher in the tree
--   As exposed by modifyM, the head of the tree is given mempty.
modifyM :: (AST t, Monoid a) => (a -> t -> (t, a)) -> t -> t
modifyM f = go f mempty
  where go :: (AST t, Monoid a) => (a -> t -> (t, a)) -> a -> t -> t
        go f m t = let (t', m') = f m t
                       ms = m `mappend` m'
                   in modifyChildren (go f ms) t'

-- | Modify Fixed Point
--   Runs the given function f on the node t, t until t = f t, then does the
--   same on all decendants of t recursively.
modifyFix :: (AST t, Eq t) => (t -> t) -> t -> t
modifyFix f t = let t' = f t
                in if t == t'
                   then modifyChildren (modifyFix f) t'
                   else modifyFix f t'

-- | Monoidic Modify Fixed Point
--   Combines the methods of modifyM and modifyFix.
--   Runs until t == t', but does not consider the Monoid's value. However, the
--   mappend still occurs each time an iteration is performed on a given AST.
modifyFixM :: (AST t, Eq t, Monoid a) => (a -> t -> (t, a)) -> t -> t
modifyFixM f = go f mempty
  where go :: (AST t, Eq t, Monoid a) => (a -> t -> (t, a)) -> a -> t -> t
        go f m t = let (t', m') = f m t
                       ms = m `mappend` m'
                   in if t == t'
                      then modifyChildren (go f ms) t'
                      else go f ms t'

-- | Evaluation
--   Recursively runs the given function on each node, top down. Uses mappend
--   to combine the results after evaluation of the entire tree.
eval :: (AST t, Monoid a) => (t -> a) -> t -> a
eval f t = (f t) `mappend` (go (eval f) t)
  where go :: (AST t, Monoid a) => (t -> a) -> t -> a
        go f = mconcat . (map f) . children 

-- | Instance Expr of AST
instance AST Expr where
    children (Lam b e t)   = [e]
    children (Let bs e)    = (map snd bs) ++ [e]
    children (App f a)     = [f, a]
    children (Case m as t) = m:(map snd as)
    children (Spec c e)    = [c, e]
    children otherwise     = []

    modifyChildren f (Lam b e t)   = Lam b (f e) t
    modifyChildren f (Let bs e)    = Let (map (\(k, v) -> (k, f v)) bs) (f e)
    modifyChildren f (App l r)     = App (f l) (f r)
    modifyChildren f (Case m as t) = Case (f m) (map (\(a,e) -> (a,f e)) as) t
    modifyChildren f (Spec c e)    = Spec (f c) (f e)
    modifyChildren f e = e

instance AST Type where
    children (TyFun tf ta)   = [tf, ta]
    children (TyApp tf ta)   = [tf, ta]
    children (TyConApp n ts) = ts
    children (TyAlg n ds)    = getASTs ds
    children (TyForAll n t)  = [t]
    children t = []

    modifyChildren f (TyFun tf ta)   = TyFun (f tf) (f ta)
    modifyChildren f (TyApp tf ta)   = TyApp (f tf) (f ta)
    modifyChildren f (TyConApp n ts) = TyConApp n (map f ts)
    modifyChildren f (TyAlg n ds)    =
        TyAlg n (map (\(DataCon n i t ts) -> DataCon n i (f t) (map f ts)) ds)
    modifyChildren f (TyForAll n t)  = TyForAll n (f t)
    modifyChildren f e = e

-- | AST Container
--   For types that contain ASTs, but that are not ASTs themselves. Such types
--   may include environments, state, and the like.
class AST t => ASTContainer c t where
    -- | Get ASTs
    --   Gets all the ASTs that are recursively contained in the container.
    getASTs :: c -> [t]
    -- | Modify ASTs
    --   Calls the function recursively on all ASTs in the container.
    modifyASTs :: (t -> t) -> c -> c

-- | Modify Container
--   Runs modify on all the ASTs in the container.
modifyContainer :: ASTContainer t e => (e -> e) -> t -> t
modifyContainer f = modifyASTs (modify f)

-- | Monoidic Modify Container
--   Runs modifyM on all the ASTs in the container.
modifyContainerM :: (ASTContainer t e, Monoid a) => (a -> e -> (e,a)) -> t -> t
modifyContainerM f = modifyASTs (modifyM f)

-- | Modify Container Fixed Point
--   Runs modifyFix on all the ASTs in the container.
modifyContainerFix :: (ASTContainer t e, Eq e) => (e -> e) -> t -> t
modifyContainerFix f = modifyASTs (modifyFix f)

-- | Evaluate Container with Function
--   Runs a function on all the ASTs in the container, and uses mappend to
--   combine the results.
evalContainerF :: (ASTContainer t e, Monoid a) => (e -> a) -> t -> a
evalContainerF f = mconcat . map f . getASTs

-- | Evaluate Container ASTs
--   Runs eval on all the ASTs in the container, and uses mappend to combine
--   the results.
evalContainerASTs :: (ASTContainer t e, Monoid a) => (e -> a) -> t -> a
evalContainerASTs f = evalContainerF (eval f)

-- | Instance ASTContainer of Itself
--   Every AST is defined as an ASTContainer of itself. Generally, functions
--   should be written using the ASTContainer typeclass.
instance AST t => ASTContainer t t where
    getASTs t = [t]
    modifyASTs f t = f t

instance ASTContainer Expr Type where
    getASTs = eval go
      where go (Var _ t)     = [t]
            go (Lam _ _ t)   = [t]
            go (Data dc)     = getASTs dc
            go (Case _ as t) = ((getASTs . map fst) as) ++ [t]
            go (Type t)      = [t]
            go _ = []

    modifyASTs f (Var n t)     = Var n (f t)
    modifyASTs f (Lam b e t)   = Lam b e (f t)
    modifyASTs f (Data dc)     = Data (modifyASTs f dc)
    modifyASTs f (Case m as t) = Case m as (f t)
    modifyASTs f (Type t)      = Type (f t)
    modifyASTs f e = e

instance ASTContainer Type Expr where
    getASTs _ = []
    modifyASTs _ t = t

instance ASTContainer State Expr where
    getASTs s = ((getASTs . type_env) s) ++
                ((getASTs . expr_env) s) ++
                ((getASTs . curr_expr) s) ++
                ((getASTs . path_cons) s) ++
                ((getASTs  . sym_links) s)

    modifyASTs f s = s { type_env  = (modifyASTs f . type_env) s
                       , expr_env  = (modifyASTs f . expr_env) s
                       , curr_expr = (modifyASTs f . curr_expr) s
                       , path_cons = (modifyASTs f . path_cons) s
                       , sym_links = (modifyASTs f . sym_links) s }

instance ASTContainer State Type where
    getASTs s = ((getASTs . type_env) s) ++
                ((getASTs . expr_env) s) ++
                ((getASTs . curr_expr) s) ++
                ((getASTs . path_cons) s) ++
                ((getASTs . sym_links) s)

    modifyASTs f s = s { type_env  = (modifyASTs f . type_env) s
                       , expr_env  = (modifyASTs f . expr_env) s
                       , curr_expr = (modifyASTs f . curr_expr) s
                       , path_cons = (modifyASTs f . path_cons) s
                       , sym_links = (modifyASTs f . sym_links) s }

instance ASTContainer DataCon Type where
    getASTs (DataCon _ _ t ts) = getASTs (t:ts)
    getASTs _ = []

    modifyASTs f (DataCon n i t ts) = DataCon n i (f t) (map f ts)
    modifyASTs _ dc = dc

instance ASTContainer Alt Expr where
    getASTs _ = []
    modifyASTs _ a = a

instance ASTContainer Alt Type where
    getASTs (Alt x) = (getASTs . fst) x
    modifyASTs f (Alt (dc, n)) = Alt (modifyASTs f dc, n)

instance ASTContainer c t => ASTContainer [c] t where
    getASTs = concatMap getASTs
    modifyASTs f = map (modifyASTs f)

instance ASTContainer c t => ASTContainer (M.Map k c) t where
    getASTs = concatMap getASTs . M.elems
    modifyASTs f = M.map (modifyASTs f)

instance (ASTContainer c1 t, ASTContainer c2 t) => ASTContainer (c1, c2) t where
    getASTs (x, y) = getASTs x ++ getASTs y
    modifyASTs f (x, y) = (modifyASTs f x, modifyASTs f y)

instance (ASTContainer a e, ASTContainer b e, ASTContainer c e) => ASTContainer (a, b, c) e where
    getASTs (x, y, z) = getASTs x ++ getASTs y ++ getASTs z
    modifyASTs f (x, y, z) = (modifyASTs f x, modifyASTs f y, modifyASTs f z)

instance (ASTContainer t e) => ASTContainer (Maybe t) e where
    getASTs (Just x) = getASTs x
    getASTs Nothing = []

    modifyASTs f (Just x) = Just (modifyASTs f x)
    modifyASTs _ Nothing = Nothing

-- | Miscellaneous Instances
--   These instances exist so that we can use them in other types that contain
--   ASTs and still consider those types ASTContainers. For example (Expr, Bool)
--   should be an ASTContainer.
instance ASTContainer Bool Expr where
    getASTs _ = []
    modifyASTs _ s = s

instance ASTContainer Bool Type where
    getASTs _ = []
    modifyASTs _ s = s

instance ASTContainer Char Expr where
    getASTs _ = []
    modifyASTs _ s = s

instance ASTContainer Char Type where
    getASTs _ = []
    modifyASTs _ s = s

instance ASTContainer Int Expr where
    getASTs _ = []
    modifyASTs _ s = s

instance ASTContainer Int Type where
    getASTs _ = []
    modifyASTs _ s = s

