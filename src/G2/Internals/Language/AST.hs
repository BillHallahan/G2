-- | Abstract Syntax Tree
--   Defines typeclasses and functions for ease of AST manipulation.

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.AST
    ( module G2.Internals.Language.AST
    ) where

import G2.Internals.Language.Syntax
import G2.Internals.Language.Support

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
    where
        go :: (AST t, Eq t, Monoid a) => (a -> t -> (t, a)) -> a -> t -> t
        go f m t =  let
                        (t', m') = f m t
                        ms = m `mappend` m'
                    in
                    if t == t'
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
    children (App f a)     = [f, a]
    children (Lam _ e)     = [e]
    children (Let bnd e)   = e : bndExprs bnd
        where
            bndExprs :: Bind -> [Expr]
            bndExprs (Bind _ kvs) = map snd kvs
    children (Case m _ as) = m : map (\(Alt _ _ e) -> e) as
    children _             = []

    modifyChildren f (App fx ax)   = App (f fx) (f ax)
    modifyChildren f (Lam b e)     = Lam b (f e)
    modifyChildren f (Let bnd e)   = Let (mapBnd f bnd) (f e)
        where
            mapBnd :: (Expr -> Expr) -> Bind -> Bind
            mapBnd f (Bind r kvs) = Bind r (map (\(k, v) -> (k, f v)) kvs)
    modifyChildren f (Case m b as) = Case (f m) b (mapAlt f as)
        where 
            mapAlt :: (Expr -> Expr) -> [Alt] -> [Alt]
            mapAlt f alts = map (\(Alt ac ps e) -> Alt ac ps (f e)) alts

    modifyChildren _ e             = e

{-

instance AST Type where
    children (TyFun tf ta)   = [tf, ta]
    children (TyApp tf ta)   = [tf, ta]
    children (TyConApp _ ts) = ts
    children (TyForAll _ t)  = [t]
    children _               = []

    modifyChildren f (TyFun tf ta)   = TyFun (f tf) (f ta)
    modifyChildren f (TyApp tf ta)   = TyApp (f tf) (f ta)
    modifyChildren f (TyConApp b ts) = TyConApp b (map f ts)
    modifyChildren f (TyForAll b t)  = TyForAll b (f t)
    modifyChildren _ t               = t

-}

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
            go (Data dc) = containedASTs dc
            go (Lam b e) = containedASTs b ++ containedASTs e
            go (Let bnd e) = containedASTs bnd ++ containedASTs e
            go (Case e i as) = (containedASTs e) ++ (containedASTs i) ++ (containedASTs as)
            go (Type t) = [t]
            go _ = []

    modifyContainedASTs f = modify (go)
      where
            go :: Expr -> Expr
            go (Var i) = Var (modifyContainedASTs f i)
            go (Data dc) = Data (modifyContainedASTs f dc)
            go (App fx ax) = App (modifyContainedASTs f fx) (modifyContainedASTs f ax)
            go (Lam b e) = Lam (modifyContainedASTs f b) (modifyContainedASTs f e)
            go (Data dc) = Data (modifyContainedASTs f dc)
            go (Case m b as) = Case (modifyContainedASTs f m) (modifyContainedASTs f b) (modifyContainedASTs f as) 
            go (Type t) = Type (f t)
            go e = e

instance ASTContainer Id Type where
  containedASTs (Id n t) = [t]

  modifyContainedASTs f (Id n t) = Id n (modifyContainedASTs f t)
  

instance ASTContainer Type Expr where
    containedASTs _ = []
    modifyContainedASTs _ t = t


instance ASTContainer State Expr where
    containedASTs s = ((containedASTs . type_env) s) ++
                      ((containedASTs . expr_env) s) ++
                      ((containedASTs . curr_expr) s) ++
                      ((containedASTs . path_conds) s) ++
                      ((containedASTs . sym_links) s)

    modifyContainedASTs f s = s { type_env  = (modifyASTs f . type_env) s
                                , expr_env  = (modifyASTs f . expr_env) s
                                , curr_expr = (modifyASTs f . curr_expr) s
                                , path_conds = (modifyASTs f . path_conds) s
                                , sym_links = (modifyASTs f . sym_links) s }


instance ASTContainer State Type where
    containedASTs s = ((containedASTs . type_env) s) ++
                      ((containedASTs . expr_env) s) ++
                      ((containedASTs . curr_expr) s) ++
                      ((containedASTs . path_conds) s) ++
                      ((containedASTs . sym_links) s)

    modifyContainedASTs f s = s { type_env  = (modifyASTs f . type_env) s
                                , expr_env  = (modifyASTs f . expr_env) s
                                , curr_expr = (modifyASTs f . curr_expr) s
                                , path_conds = (modifyASTs f . path_conds) s
                                , sym_links = (modifyASTs f . sym_links) s }


instance ASTContainer Bind Expr where
    containedASTs (Bind _ ie) = containedASTs ie

    modifyContainedASTs f (Bind r ie) = Bind r (modifyContainedASTs f ie)

instance ASTContainer Bind Type where
    containedASTs (Bind _ ie) = containedASTs ie

    modifyContainedASTs f (Bind r ie) = Bind r (modifyContainedASTs f ie)

instance ASTContainer DataCon Type where
    containedASTs (DataCon _ t ts) = containedASTs (t:ts)
    containedASTs _ = []

    modifyContainedASTs f (DataCon n t ts) = DataCon n (f t) (map f ts)
    modifyContainedASTs _ dc = dc

instance ASTContainer AltCon Expr where
    containedASTs _ = []
    modifyContainedASTs _ e = e

instance ASTContainer AltCon Type where
    containedASTs (DataAlt dc) = containedASTs dc
    containedASTs _ = []

    modifyContainedASTs f (DataAlt dc) = DataAlt (modifyContainedASTs f dc)
    modifyContainedASTs _ e = e

instance ASTContainer Alt Expr where
    containedASTs (Alt _ _ e) = [e]
    modifyContainedASTs f (Alt a i e) = Alt a i (f e)

instance ASTContainer Alt Type where
    containedASTs (Alt a i e) = (containedASTs a) ++ (containedASTs i) ++ (containedASTs e)
    modifyContainedASTs f (Alt a i e) =
        Alt (modifyContainedASTs f a) (modifyContainedASTs f i) (modifyContainedASTs f e)

instance ASTContainer SymLinks Expr where
    containedASTs _ = []
    modifyContainedASTs _ m = m

instance ASTContainer SymLinks Type where
    containedASTs (SymLinks m) = map (\(_, t, _) -> t) $ M.elems m
    modifyContainedASTs f (SymLinks m) =
        SymLinks (M.map (\(n, t, i) -> (n, modifyContainedASTs f t, i)) m)

instance ASTContainer PathCond Expr where
    containedASTs (ExtCond e _)   = [e]
    containedASTs (AltCond e _ _) = [e]

    modifyContainedASTs f (ExtCond e b)   = ExtCond (modifyContainedASTs f e) b
    modifyContainedASTs f (AltCond e a b) = AltCond (modifyContainedASTs f e) a b

instance ASTContainer PathCond Type where
    containedASTs (ExtCond e _)   = containedASTs e
    containedASTs (AltCond e a _) = containedASTs e ++ containedASTs a

    modifyContainedASTs f (ExtCond e b) = ExtCond (modifyContainedASTs f e) b
    modifyContainedASTs f (AltCond e a b) =
        AltCond (modifyContainedASTs f e) (modifyContainedASTs f a) b

instance (Foldable f, Functor f, ASTContainer c t) => ASTContainer (f c) t where
    containedASTs = foldMap (containedASTs)

    modifyContainedASTs f = fmap (modifyContainedASTs f)

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
