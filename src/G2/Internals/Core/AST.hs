-- | AST
--   Defines typeclasses and functions for ease of AST manipulation.

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Core.AST where

import G2.Internals.Core.Language

import qualified Data.Map as M

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
eval f t = (f t) `mappend` (evalChildren (eval f) t)

-- | Evaluation of Children
evalChildren :: (AST t, Monoid a) => (t -> a) -> t -> a
evalChildren f = mconcat . (map f) . children

-- | AST Container
--   For types that contain ASTs, but that are not ASTs themselves. Such types
--   may include environments, state, and the like.
class AST t => ASTContainer c t where
    -- | Contained ASTs
    --   Gets all the ASTs that are recursively contained in the container.
    containedASTs :: c -> [t]
    -- | Modify Contained ASTs
    --   Calls the function on all ASTs in the container.
    modifyContainedASTs :: (t -> t) -> c -> c

-- | Modify Container
--   Runs modify on all the ASTs in the container.
modifyASTs :: ASTContainer t e => (e -> e) -> t -> t
modifyASTs f = modifyContainedASTs (modify f)

-- | Monoidic Modify Container
--   Runs modifyM on all the ASTs in the container.
modifyASTsM :: (ASTContainer t e, Monoid a) => (a -> e -> (e,a)) -> t -> t
modifyASTsM f = modifyContainedASTs (modifyM f)

-- | Modify Container Fixed Point
--   Runs modifyFix on all the ASTs in the container.
modifyASTsFix :: (ASTContainer t e, Eq e) => (e -> e) -> t -> t
modifyASTsFix f = modifyContainedASTs (modifyFix f)

-- | Evaluate Container ASTs
--   Runs eval on all the ASTs in the container, and uses mappend to combine
--   the results.
evalASTs :: (ASTContainer t e, Monoid a) => (e -> a) -> t -> a
evalASTs f = evalContainedASTs (eval f)

-- | Evaluate Container with Function
--   Runs a function on all the ASTs in the container, and uses mappend to
--   combine the results.
evalContainedASTs :: (ASTContainer t e, Monoid a) => (e -> a) -> t -> a
evalContainedASTs f = mconcat . map f . containedASTs

-- | Instance Expr of AST
instance AST Expr where
    children (Lam _ e _)   = [e]
    children (Let bs e)    = (map snd bs) ++ [e]
    children (App f a)     = [f, a]
    children (Case m as _) = m:(map snd as)
    children (Spec c e)    = [c, e]
    children _ = []

    modifyChildren f (Lam b e t)   = Lam b (f e) t
    modifyChildren f (Let bs e)    = Let (map (\(k, v) -> (k, f v)) bs) (f e)
    modifyChildren f (App l r)     = App (f l) (f r)
    modifyChildren f (Case m as t) = Case (f m) (map (\(a,e) -> (a,f e)) as) t
    modifyChildren f (Spec c e)    = Spec (f c) (f e)
    modifyChildren f e = e

instance AST Type where
    children (TyFun tf ta)   = [tf, ta]
    children (TyApp tf ta)   = [tf, ta]
    children (TyConApp _ ts) = ts
    children (TyAlg _ dcs)   = containedASTs dcs
    children (TyForAll _ t)  = [t]
    children _ = []

    modifyChildren f (TyFun tf ta)   = TyFun (f tf) (f ta)
    modifyChildren f (TyApp tf ta)   = TyApp (f tf) (f ta)
    modifyChildren f (TyConApp n ts) = TyConApp n (map f ts)
    modifyChildren f (TyAlg n dcs)   =
        TyAlg n (map (\(DataCon n i t ts) -> DataCon n i (f t) (map f ts)) dcs)
    modifyChildren f (TyForAll n t)  = TyForAll n (f t)
    modifyChildren f e = e

-- | Instance ASTContainer of Itself
--   Every AST is defined as an ASTContainer of itself. Generally, functions
--   should be written using the ASTContainer typeclass.
instance AST t => ASTContainer t t where
    containedASTs t = [t]
    modifyContainedASTs f t = f t

instance ASTContainer Expr Type where
    containedASTs = eval go
      where go (Var _ t)     = [t]
            go (Lam _ _ t)   = [t]
            go (Data dc)     = containedASTs dc
            go (Case _ as t) = ((containedASTs . map fst) as) ++ [t]
            go (Type t)      = [t]
            go _ = []

    modifyContainedASTs f = modify (go f)
      where go f (Var n t)     = Var n (f t)
            go f (Lam b e t)   = Lam b e (f t)
            go f (Data dc)     = Data (modifyContainedASTs f dc)
            go f (Case m as t) = Case m as (f t)
            go f (Type t)      = Type (f t)
            go f e = e

instance ASTContainer Type Expr where
    containedASTs _ = []
    modifyContainedASTs _ t = t

instance ASTContainer State Expr where
    containedASTs s = ((containedASTs . type_env) s) ++
                      ((containedASTs . expr_env) s) ++
                      ((containedASTs . curr_expr) s) ++
                      ((containedASTs . path_cons) s) ++
                      ((containedASTs . sym_links) s)

    modifyContainedASTs f s = s { type_env  = (modifyASTs f . type_env) s
                                , expr_env  = (modifyASTs f . expr_env) s
                                , curr_expr = (modifyASTs f . curr_expr) s
                                , path_cons = (modifyASTs f . path_cons) s
                                , sym_links = (modifyASTs f . sym_links) s }

instance ASTContainer State Type where
    containedASTs s = ((containedASTs . type_env) s) ++
                      ((containedASTs . expr_env) s) ++
                      ((containedASTs . curr_expr) s) ++
                      ((containedASTs . path_cons) s) ++
                      ((containedASTs . sym_links) s)

    modifyContainedASTs f s = s { type_env  = (modifyASTs f . type_env) s
                                , expr_env  = (modifyASTs f . expr_env) s
                                , curr_expr = (modifyASTs f . curr_expr) s
                                , path_cons = (modifyASTs f . path_cons) s
                                , sym_links = (modifyASTs f . sym_links) s }

instance ASTContainer DataCon Type where
    containedASTs (DataCon _ _ t ts) = containedASTs (t:ts)
    containedASTs _ = []

    modifyContainedASTs f (DataCon n i t ts) = DataCon n i (f t) (map f ts)
    modifyContainedASTs _ dc = dc

instance ASTContainer Alt Expr where
    containedASTs _ = []
    modifyContainedASTs _ a = a

instance ASTContainer Alt Type where
    containedASTs (Alt x) = (containedASTs . fst) x
    modifyContainedASTs f (Alt (dc, n)) = Alt (modifyContainedASTs f dc, n)

instance ASTContainer c t => ASTContainer [c] t where
    containedASTs = concatMap containedASTs
    modifyContainedASTs f = map (modifyContainedASTs f)

instance ASTContainer c t => ASTContainer (M.Map k c) t where
    containedASTs = concatMap containedASTs . M.elems
    modifyContainedASTs f = M.map (modifyContainedASTs f)

instance (ASTContainer a t, ASTContainer b t) => ASTContainer (a, b) t where
    containedASTs (x, y) = containedASTs x ++ containedASTs y
    modifyContainedASTs f (x, y) = (modifyContainedASTs f x,
                                    modifyContainedASTs f y)

instance (ASTContainer a t,
          ASTContainer b t,
          ASTContainer c t) => ASTContainer (a, b, c) t where
    containedASTs (x, y, z) = containedASTs x ++
                              containedASTs y ++
                              containedASTs z
    modifyContainedASTs f (x, y, z) = (modifyContainedASTs f x,
                                       modifyContainedASTs f y,
                                       modifyContainedASTs f z)

instance (ASTContainer c t) => ASTContainer (Maybe c) t where
    containedASTs (Just x) = containedASTs x
    containedASTs Nothing = []

    modifyContainedASTs f (Just x) = Just (modifyContainedASTs f x)
    modifyContainedASTs _ Nothing = Nothing

-- | Miscellaneous Instances
--   These instances exist so that we can use them in other types that contain
--   ASTs and still consider those types ASTContainers. For example (Expr, Bool)
--   should be an ASTContainer.
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

