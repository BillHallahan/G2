-- | ASTHandler
-- This module provides two type classes and several higher order functions to ease the handling of ASTs
-- (in particular, Expr and Types.)
-- See tests/UnitTests.hs for examples.

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Core.ASTHandler where

import qualified Data.Map as M

import G2.Internals.Core.Language

class AST t where
    -- Gets the direct children of the given node
    children :: t -> [t]

    -- Applies the given function to all children of the given node
    modifyChildren :: (t -> t) -> t -> t

-- Calls the given function on the given node, and all of the new nodes decendants, recursively
modify :: AST t => (t -> t) -> t -> t
modify f e = modifyChildren (modify f) $ f e

-- Similar to modify, but also passes a Monoid instance to the modify function. 
-- Children have access to the mconcated results from higher in the tree
-- As exposed by modify', the head of the tree is given mempty
modify' :: (AST t, Monoid a) => (a -> t -> (t, a)) -> t -> t
modify' f = modify'' f mempty
    where
        modify'' :: (AST t, Monoid a) => (a -> t -> (t, a)) -> a -> t -> t
        modify'' f x e =
            let
                (e', x') = f x e
                x'' = x `mappend` x'
            in
            modifyChildren (modify'' f x'') e'

-- Runs the given function f on the node e, e until e = f e
-- then does the same on all decendants of e, recursively
modifyFixed :: (AST t, Eq t) => (t -> t) -> t -> t
modifyFixed f e =
    let
            e' = f e
    in
    if e == e' then modifyChildren (modifyFixed f) e' else modifyFixed f e'

-- Combines the methods of modify' and modifyFixed
-- Runs until e == e', but does not consider the Monoid's value
-- however, the mappend still occurs each time an iteration is performed on a given AST
modifyFixed' :: (AST t, Eq t, Monoid a) => (a -> t -> (t, a)) -> t -> t
modifyFixed' f = modifyFixed'' f mempty
    where
        modifyFixed'' :: (AST t, Eq t, Monoid a) => (a -> t -> (t, a)) -> a -> t -> t
        modifyFixed'' f x e =
            let
                (e', x') = f x e
                x'' = x `mappend` x'
            in
            if e == e' then modifyChildren (modifyFixed'' f x'') e' else modifyFixed'' f x'' e'

-- Runs the given function on each child and uses mappend to combine the results
evalChildren :: (AST t, Monoid a) => (t -> a) -> t -> a
evalChildren f = mconcat . map f . children 

-- Recursively runs the given function on each node, top down, and uses mappend to combine the results
eval :: (AST t, Monoid a) => (t -> a) -> t -> a
eval f e = mappend (f e) . evalChildren (eval f) $ e

instance AST Expr where
    children (Lam _ e _) = [e]
    children (Let ne e) = map snd ne ++ [e]
    children (App e e') = [e, e']
    children (Case e ae _) = e:map snd ae
    children (Spec e e') = [e, e']
    children _ = []

    modifyChildren f (Lam n e t) = Lam n (f e) t
    modifyChildren f (Let ne e) = Let (map (\(n, e') -> (n, f e')) ne) (f e)
    modifyChildren f (App e e') = App (f e) (f e')
    modifyChildren f (Case e ae t) = Case (f e) (map (\(a, e') -> (a, f e')) ae) t
    modifyChildren f (Spec e e') = Spec (f e) (f e')
    modifyChildren _ e = e

instance AST Type where
    children (TyFun t t') = [t, t']
    children (TyApp t t') = [t, t']
    children (TyConApp _ ts) = ts
    children (TyAlg _ ds) = contains ds
    children (TyForAll _ t) = [t]
    children _ = []

    modifyChildren f (TyFun t t') = TyFun (f t) (f t')
    modifyChildren f (TyApp t t') = TyApp (f t) (f t')
    modifyChildren f (TyConApp n ts) = TyConApp n (map f ts)
    modifyChildren f (TyAlg n ds) = TyAlg n (map (\(DataCon n i t ts) -> DataCon n i (f t) (map f ts)) ds)
    modifyChildren f (TyForAll n t) = TyForAll n (f t)
    modifyChildren _ e = e

--This is for types that contain ASTs, but that are not ASTs themselves.
-- I.e., the expression environment, or a State
class AST e => ASTContainer t e where
    -- Get's all ASTs that are directly contained in t,
    -- plus all the contains of some ASTContainer in t
    -- (i.e. we recursively check all ASTContainers in t, and find the "top" of all ASTs)
    contains :: t -> [e]

    -- Calls the given function on all ASTs in contains t
    modifyTopContains :: (e -> e) -> t -> t

-- Runs modify on all the ASTs in the container
modifyContains :: ASTContainer t e => (e -> e) -> t -> t
modifyContains f x = modifyTopContains (modify f) $ x

-- Runs modify' on all the ASTs in the container
modifyContains' :: (ASTContainer t e, Monoid a) => (a -> e -> (e, a)) -> t -> t
modifyContains' f = modifyTopContains (modify' f)

-- Runs modifyFixed on all the ASTs in the container
modifyContainsFixed :: (ASTContainer t e, Eq e) => (e -> e) -> t -> t
modifyContainsFixed f = modifyTopContains (modifyFixed f)

-- Runs a function on all the ASTs in the container, and uses mappend to combine the results
evalTopContains :: (ASTContainer t e, Monoid a) => (e -> a) -> t -> a
evalTopContains f x = mconcat . map f . contains $ x

-- Runs eval on all the ASTs in the container, and uses mappend to combine the results
evalContains :: (ASTContainer t e, Monoid a) => (e -> a) -> t -> a
evalContains f x = evalTopContains (eval f) $ x

-- Every AST is defined as an ASTContainer of itself
-- Generally, functions should be written using the ASTContainer typeclass
instance AST e => ASTContainer e e where
    contains e = [e]
    modifyTopContains f e = f e

instance ASTContainer Expr Type where
    contains = eval contains'
        where
            contains' (Var _ t) = [t]
            contains' (Lam _ _ t) = [t]
            contains' (Data dc) = contains dc
            contains' (Case _ ae t) = (contains . map fst $ ae) ++ [t]
            contains' (Type t) = [t]
            contains' _ = []

    modifyTopContains f (Var n t) = Var n (f t)
    modifyTopContains f (Lam n e t) = Lam n e (f t)
    modifyTopContains f (Data dc) = Data (modifyTopContains f dc)
    modifyTopContains f (Case n ae t) = Case n ae (f t)
    modifyTopContains f (Type t) = Type (f t)
    modifyTopContains f e = e

instance ASTContainer Type Expr where
    contains _ = []
    modifyTopContains _ t = t

instance ASTContainer State Expr where
    contains s = (contains . type_env $ s)
              ++ (contains . expr_env $ s)
              ++ (contains . curr_expr $ s)
              ++ (contains . path_cons $ s)
              ++ (contains  . sym_links $ s)

    modifyTopContains f s =
        s { 
              type_env = modifyTopContains f . type_env $ s
            , expr_env = modifyTopContains f . expr_env $ s
            , curr_expr = modifyTopContains f . curr_expr $ s
            , path_cons = modifyTopContains f . path_cons $ s
            , sym_links = modifyTopContains f . sym_links $ s
          }

instance ASTContainer State Type where
    contains s = (contains . type_env $ s)
              ++ (contains . expr_env $ s)
              ++ (contains . curr_expr $ s)
              ++ (contains . path_cons $ s)
              ++ (contains  . sym_links $ s)

    modifyTopContains f s =
        s { 
              type_env = modifyTopContains f . type_env $ s
            , expr_env = modifyTopContains f . expr_env $ s
            , curr_expr = modifyTopContains f . curr_expr $ s
            , path_cons = modifyTopContains f . path_cons $ s
            , sym_links = modifyTopContains f . sym_links $ s
          }

instance ASTContainer DataCon Type where
    contains (DataCon _ _ t ts) = contains (t:ts)
    contains _ = []

    modifyTopContains f (DataCon n i t ts) = DataCon n i (f t) (map f ts)
    modifyTopContains _ dc = dc

instance ASTContainer Alt Expr where
    contains _ = []
    modifyTopContains _ a = a

instance ASTContainer Alt Type where
    contains (Alt x) = contains . fst $ x
    modifyTopContains f (Alt (dc, n)) = Alt (modifyTopContains f dc, n)

instance ASTContainer t e => ASTContainer [t] e where
    contains = concatMap contains
    modifyTopContains f = map (modifyTopContains f)

instance ASTContainer t e => ASTContainer (M.Map k t) e where
    contains = concatMap contains . M.elems
    modifyTopContains f = M.map (modifyTopContains f)

instance (ASTContainer a e, ASTContainer b e) => ASTContainer (a, b) e where
    contains (x, y) = contains x ++ contains y
    modifyTopContains f (x, y) = (modifyTopContains f x, modifyTopContains f y)

instance (ASTContainer a e, ASTContainer b e, ASTContainer c e) => ASTContainer (a, b, c) e where
    contains (x, y, z) = contains x ++ contains y ++ contains z
    modifyTopContains f (x, y, z) = (modifyTopContains f x, modifyTopContains f y, modifyTopContains f z)

instance (ASTContainer t e) => ASTContainer (Maybe t) e where
    contains (Just x) = contains x
    contains Nothing = []

    modifyTopContains f (Just x) = Just (modifyTopContains f x)
    modifyTopContains _ Nothing = Nothing

-- These instances exist so that we can use them in other types that contain ASTs,
-- and still consider those types ASTContainers
-- For example (Expr, Bool) should be an ASTContainer
instance ASTContainer Bool Expr where
    contains _ = []
    modifyTopContains _ s = s

instance ASTContainer Bool Type where
    contains _ = []
    modifyTopContains _ s = s

instance ASTContainer Char Expr where
    contains _ = []
    modifyTopContains _ s = s

instance ASTContainer Char Type where
    contains _ = []
    modifyTopContains _ s = s

instance ASTContainer Int Expr where
    contains _ = []
    modifyTopContains _ s = s

instance ASTContainer Int Type where
    contains _ = []
    modifyTopContains _ s = s