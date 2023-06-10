-- | Defines typeclasses and functions to make it easier to write functions that require traversing ASTs.

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module G2.Language.AST
    ( AST (..)
    , modify
    , modifyMonoid
    , modifyFix
    , modifyMaybe
    , modifyContainedFix
    , modifyFixMonoid
    , eval
    , evalMonoid
    , evalChildren
    , ASTContainer (..)
    , modifyASTs
    , modifyASTsMonoid
    , modifyASTsFix
    , modifyContainedASTsFix
    , evalASTs
    , evalASTsMonoid
    , evalContainedASTs
    , replaceASTs
    ) where

import qualified G2.Data.UFMap as UF
import G2.Language.Syntax
import G2.Language.AlgDataTy

import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.Map as M
import qualified Data.Text as T

-- | Describes data types that define an AST.
class AST t where
    -- | Gets the direct children of the given node.
    children :: t -> [t]
    -- | Applies the given function to all direct children of the given node.
    modifyChildren :: (t -> t) -> t -> t


-- | Calls the given function on the given node, and all of the descendants
-- top down recursively.
-- Typically, the passed higher order function will modify some subset
-- of the constructors of the given type, and leave the rest unchanged.
--
-- >>> let go e = case e of Var (Id _ t) -> SymGen t; _ -> e
-- >>> let n = Name "x" Nothing 0 Nothing
-- >>> modify go (Lam TypeL (Id n TyLitInt) (App (Var $ Id n TyLitInt) (Var $ Id n TyLitFloat)))
-- Lam TypeL (Id (Name "x" Nothing 0 Nothing) TyLitInt) (App (SymGen TyLitInt) (SymGen TyLitFloat))
modify :: AST t => (t -> t) -> t -> t
modify f t = go t
    where
        go t' = modifyChildren go (f t')

{-# SPECIALISE modify :: (Expr -> Expr) -> Expr -> Expr #-}
{-# SPECIALISE modify :: (Type -> Type) -> Type -> Type #-}

-- | Similar to modify. Also passes a Monoid instance to the modify function. 
-- Children have access to the mconcated results from higher in the tree
-- The head of the tree is given mempty.
modifyMonoid :: (AST t, Monoid a) => (a -> t -> (t, a)) -> t -> t
modifyMonoid f = go mempty
  where
    go m t = let (t', m') = f m t
                 ms = m `mappend` m'
             in modifyChildren (go ms) t'

-- | Runs the given function f on the node t, t until t = f t, then does the
-- same on all decendants of t recursively.
modifyFix :: (AST t, Eq t) => (t -> t) -> t -> t
modifyFix f t = go t
    where
        go t' = let t'' = f t'
                in if t' == t'' then modifyChildren go t'' else go t''

-- | Runs the given function f on the node t repeatedly, until f t = Nothing, then does the
-- same on all decendants of t recursively.
modifyMaybe :: AST t => (t -> Maybe t) -> t -> t
modifyMaybe f = go
    where
        go t = let mt = f t in
                case mt of
                    Just v -> go v
                    Nothing -> modifyChildren go t

-- | Runs the given function f on the node t, t until t = f t
modifyContainedFix :: (AST t, Eq t, Show t) => (t -> t) -> t -> t
modifyContainedFix f t = let t' = f t
                in if t == t'
                    then t'
                    else modifyContainedFix f t'

-- | Combines the methods of modifyM and modifyFix.
-- Runs until t == t', but does not consider the Monoid's value. However, the
-- mappend still occurs each time an iteration is performed on a given AST.
modifyFixMonoid :: (AST t, Eq t, Monoid a) => (a -> t -> (t, a)) -> t -> t
modifyFixMonoid f = go f mempty
  where
    go :: (AST t, Eq t, Monoid a) => (a -> t -> (t, a)) -> a -> t -> t
    go g m t =  let (t', m') = g m t
                    ms = m `mappend` m'
                in if t == t'
                    then modifyChildren (go g ms) t'
                    else go g ms t'

-- | Recursively runs the given function on each node, top down. Uses mappend
-- to combine the results after evaluation of the entire tree.
--
-- >>> let go e = case e of Lit l -> [l]; _ -> []
-- >>> plusInt = Prim Plus (TyFun TyLitInt (TyFun TyLitInt TyLitInt))
-- >>> eval go $ App (App plusInt (Lit $ LitInt 0)) (Lit $ LitInt 1)
-- [LitInt 0, LitInt 1]
{-# INLINE eval #-}
eval :: (AST t, Monoid a) => (t -> a) -> t -> a
eval f t = go t
    where
        go t' = f t' `mappend` evalChildren go t'

-- | Recursively runs the given function on each node, top down.  We collect
-- information using on Monoid, and also pass another monoid that can help 
-- accumulate results.
evalMonoid :: (AST t, Monoid a, Monoid b) => (b -> t -> (b, a)) -> t -> a
evalMonoid f = go f mempty
    where
        go :: (AST t, Monoid a, Monoid b) => (b -> t -> (b, a)) -> b -> t -> a
        go g b t = let
                        (b', a') = g b t
                        b'' = b `mappend` b'
                   in
                   a' `mappend` evalChildren (go g b'') t

-- | Evaluates all children of the given AST node with the given monoid,
-- and `mconcat`s the results
{-# INLINE evalChildren #-}
evalChildren :: (AST t, Monoid a) => (t -> a) -> t -> a
evalChildren f = mconcat . map f . children

-- | For types that may contain ASTs, but that are not ASTs themselves. Such types
-- may include environments, State, functors, etc.
class AST t => ASTContainer c t where
    -- | Gets all the ASTs that are directly contained in the container.
    containedASTs :: c -> [t]
    -- | Calls the function on all ASTs directly in the container.
    modifyContainedASTs :: (t -> t) -> c -> c

-- | Runs `modify` on all the ASTs in the container.
modifyASTs :: ASTContainer t e => (e -> e) -> t -> t
modifyASTs f = modifyContainedASTs (modify f)

-- | Runs `modifyMonoid` on all the ASTs in the container.
modifyASTsMonoid :: (ASTContainer t e, Monoid a) => (a -> e -> (e,a)) -> t -> t
modifyASTsMonoid f = modifyContainedASTs (modifyMonoid f)

-- | Runs `modifyFix` on all the ASTs in the container.
modifyASTsFix :: (ASTContainer t e, Eq e) => (e -> e) -> t -> t
modifyASTsFix f = modifyContainedASTs (modifyFix f)

-- | Runs `modifyContainedFix` on all the ASTs in the container.
modifyContainedASTsFix :: (ASTContainer t e, Eq e, Show e) => (e -> e) -> t -> t
modifyContainedASTsFix f = modifyContainedASTs (modifyContainedFix f)

-- | Runs `eval` on all the ASTs in the container, and uses mappend to results.
evalASTs :: (ASTContainer t e, Monoid a) => (e -> a) -> t -> a
evalASTs f = evalContainedASTs (eval f)

-- | Runs `evalMonoid` on all the ASTs in the container, and uses mappend to results.
evalASTsMonoid :: (ASTContainer t e, Monoid a, Monoid b) => (b -> e -> (b, a)) -> t -> a
evalASTsMonoid f = evalContainedASTs (evalMonoid f)

-- | Runs a function on all the ASTs in the container, and uses mappend to
-- combine the results.
evalContainedASTs :: (ASTContainer t e, Monoid a) => (e -> a) -> t -> a
evalContainedASTs f = mconcat . map f . containedASTs

instance AST Expr where
    children (Var _) = []
    children (Lit _) = []
    children (Prim _ _) = []
    children (Data _) = []
    children (App f a) = [f, a]
    children (Lam _ _ e) = [e]
    children (Let bind e) = e : containedASTs bind
    children (Case m _ _ as) = m : map (\(Alt _ e) -> e) as
    children (Cast e _) = [e]
    children (Coercion _) = []
    children (Type _) = []
    children (Tick _ e) = [e]
    children (NonDet es) = es
    children (SymGen _) = []
    children (Assume _ e e') = [e, e']
    children (Assert _ e e') = [e, e']

    modifyChildren f (App fx ax) = App (f fx) (f ax)
    modifyChildren f (Lam u b e) = Lam u b (f e)
    modifyChildren f (Let bind e) = Let (modifyContainedASTs f bind) (f e)
    modifyChildren f (Case m b t as) = Case (f m) b t (mapAlt f as)
      where
        mapAlt :: (Expr -> Expr) -> [Alt] -> [Alt]
        mapAlt g alts = map (\(Alt ac e) -> Alt ac (g e)) alts
    modifyChildren f (Cast e c) = Cast (f e) c
    modifyChildren f (Tick t e) = Tick t (f e)
    modifyChildren f (NonDet es) = NonDet (map f es)
    modifyChildren f (Assume is e e') = Assume (modifyContainedASTs f is) (f e) (f e')
    modifyChildren f (Assert is e e') = Assert (modifyContainedASTs f is) (f e) (f e')
    modifyChildren _ e = e

instance AST Type where
    children (TyVar i) = containedASTs i
    children (TyFun tf ta) = [tf, ta]
    children (TyApp tf ta) = [tf, ta]
    children (TyCon _ t) = [t]
    children (TyForAll b t)  = containedASTs b ++ [t]
    children _ = []

    modifyChildren f (TyVar i) = TyVar $ modifyContainedASTs f i
    modifyChildren f (TyFun tf ta) = TyFun (f tf) (f ta)
    modifyChildren f (TyApp tf ta) = TyApp (f tf) (f ta)
    modifyChildren f (TyCon b ts) = TyCon b (f ts)
    modifyChildren f (TyForAll b t) = TyForAll (modifyContainedASTs f b) (f t)
    modifyChildren _ t = t

instance AST DataCon where
    children _ = []
    modifyChildren _ (DataCon n ty) = DataCon n ty

-- | Every AST is defined as an ASTContainer of itself. Generally, functions
--   should be written using the ASTContainer typeclass.
instance AST t => ASTContainer t t where
    containedASTs t = [t]

    modifyContainedASTs f t = f t

instance ASTContainer Expr Type where
    containedASTs (Var i) = containedASTs i
    containedASTs (Prim _ t) = [t]
    containedASTs (Data dc) = containedASTs dc
    containedASTs (App e1 e2) = containedASTs e1 ++ containedASTs e2
    containedASTs (Lam _ b e) = containedASTs b ++ containedASTs e
    containedASTs (Let bnd e) = containedASTs bnd ++ containedASTs e
    containedASTs (Case e i t as) = containedASTs e ++ containedASTs i ++ containedASTs t ++ containedASTs as
    containedASTs (Cast e c) = containedASTs e ++ containedASTs c
    containedASTs (Coercion c) = containedASTs c
    containedASTs (Type t) = [t]
    containedASTs (Tick _ e) = containedASTs e
    containedASTs (NonDet es) = containedASTs es
    containedASTs (SymGen t) = [t]
    containedASTs (Assume is e e') = containedASTs is ++ containedASTs e ++ containedASTs e'
    containedASTs (Assert is e e') = containedASTs is ++ containedASTs e ++ containedASTs e'
    containedASTs _ = []

    modifyContainedASTs f (Var i) = Var (modifyContainedASTs f i)
    modifyContainedASTs f (Prim p t) = Prim p (f t)
    modifyContainedASTs f (Data dc) = Data (modifyContainedASTs f dc)
    modifyContainedASTs f (App fx ax) = App (modifyContainedASTs f fx) (modifyContainedASTs f ax)
    modifyContainedASTs f (Lam u b e) = Lam u (modifyContainedASTs f b)(modifyContainedASTs f e)
    modifyContainedASTs f (Let bnd e) = Let (modifyContainedASTs f bnd) (modifyContainedASTs f e)
    modifyContainedASTs f (Case m i t as) = Case (modifyContainedASTs f m) (modifyContainedASTs f i) (f t) (modifyContainedASTs f as) 
    modifyContainedASTs f (Type t) = Type (f t)
    modifyContainedASTs f (Cast e c) = Cast (modifyContainedASTs f e) (modifyContainedASTs f c)
    modifyContainedASTs f (Coercion c) = Coercion (modifyContainedASTs f c)
    modifyContainedASTs f (Tick t e) = Tick t (modifyContainedASTs f e)
    modifyContainedASTs f (NonDet es) = NonDet (modifyContainedASTs f es)
    modifyContainedASTs f (SymGen t) = SymGen (f t)
    modifyContainedASTs f (Assume is e e') = Assume (modifyContainedASTs f is) (modifyContainedASTs f e) (modifyContainedASTs f e')
    modifyContainedASTs f (Assert is e e') = 
        Assert (modifyContainedASTs f is) (modifyContainedASTs f e) (modifyContainedASTs f e')
    modifyContainedASTs _ e = e

instance ASTContainer LamUse Expr where
  containedASTs _ = []
  modifyContainedASTs _ i = i

instance ASTContainer LamUse Type where
  containedASTs _ = []
  modifyContainedASTs _ i = i

instance ASTContainer Id Expr where
  containedASTs (Id _ _) = []

  modifyContainedASTs _ i = i

instance ASTContainer Id Type where
  containedASTs (Id _ t) = [t]

  modifyContainedASTs f (Id n t) = Id n (f t)

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
    containedASTs (DataCon _ t) = [t]
    modifyContainedASTs f (DataCon n t) = DataCon n (f t)

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

instance ASTContainer Coercion Expr where
    containedASTs _ = []
    modifyContainedASTs _ c = c

instance ASTContainer Coercion Type where
    containedASTs (t :~ t') = [t, t']
    modifyContainedASTs f (t :~ t') = f t :~ f t'

instance ASTContainer FuncCall Expr where
    containedASTs (FuncCall { arguments = as, returns = r}) = as ++ [r]
    modifyContainedASTs f fc@(FuncCall { arguments = as, returns = r}) = 
        fc {arguments = map f as, returns = f r}

instance ASTContainer FuncCall Type where
    containedASTs (FuncCall { arguments = as, returns = r}) = containedASTs as ++ containedASTs r
    modifyContainedASTs f fc@(FuncCall { arguments = as, returns = r}) =
        fc {arguments = modifyContainedASTs f as, returns = modifyContainedASTs f r}

instance ASTContainer RewriteRule Expr where
    containedASTs (RewriteRule { ru_args = a, ru_rhs = s }) = a ++ [s]
    modifyContainedASTs f rr@(RewriteRule { ru_args = a, ru_rhs = s }) =
        rr { ru_args = modifyContainedASTs f a, ru_rhs = modifyContainedASTs f s }

instance ASTContainer RewriteRule Type where
    containedASTs (RewriteRule { ru_bndrs = b, ru_args = a, ru_rhs = s }) =
        (containedASTs b) ++ (containedASTs a) ++ (containedASTs s)
    modifyContainedASTs f rr@(RewriteRule { ru_bndrs = b, ru_args = a, ru_rhs = s }) =
        rr {
             ru_bndrs = modifyContainedASTs f b
           , ru_args = modifyContainedASTs f a
           , ru_rhs = modifyContainedASTs f s
           }

-- instance (Foldable f, Functor f, ASTContainer c t) => ASTContainer (f c) t where
--     containedASTs = foldMap (containedASTs)

--     modifyContainedASTs f = fmap (modifyContainedASTs f)

instance ASTContainer c t => ASTContainer [c] t where
    containedASTs = foldMap (containedASTs)

    modifyContainedASTs f = fmap (modifyContainedASTs f)

instance ASTContainer c t => ASTContainer (Maybe c) t where
    containedASTs = foldMap (containedASTs)

    modifyContainedASTs f = fmap (modifyContainedASTs f)


instance ASTContainer c t => ASTContainer (HM.HashMap k c) t where
    containedASTs = foldMap (containedASTs)

    modifyContainedASTs f = fmap (modifyContainedASTs f)

instance ASTContainer c t => ASTContainer (M.Map k c) t where
    containedASTs = foldMap (containedASTs)

    modifyContainedASTs f = fmap (modifyContainedASTs f)

instance (ASTContainer s t, Hashable s, Eq s) => ASTContainer (HS.HashSet s) t where
    containedASTs = containedASTs . HS.toList 

    modifyContainedASTs f = HS.map (modifyContainedASTs f)

instance ASTContainer () Expr where
    containedASTs _ = []
    modifyContainedASTs _ t = t

instance ASTContainer () Type where
    containedASTs _ = []
    modifyContainedASTs _ t = t

instance (ASTContainer c t, ASTContainer d t) => ASTContainer (c, d) t where
    containedASTs (x, y) = containedASTs x ++ containedASTs y

    modifyContainedASTs f (x, y) = (modifyContainedASTs f x, modifyContainedASTs f y)

instance
    (ASTContainer c t, ASTContainer d t, ASTContainer e t) => ASTContainer (c, d, e) t where
        containedASTs (x, y, z) = containedASTs x ++ containedASTs y ++ containedASTs z

        modifyContainedASTs f (x, y, z) = (modifyContainedASTs f x, modifyContainedASTs f y, modifyContainedASTs f z)

instance
    (ASTContainer c t, ASTContainer d t, ASTContainer e t, ASTContainer g t) => ASTContainer (c, d, e, g) t where
        containedASTs (x, y, z, w) = containedASTs x ++ containedASTs y ++ containedASTs z ++ containedASTs w

        modifyContainedASTs f (x, y, z, w) = (modifyContainedASTs f x, modifyContainedASTs f y, modifyContainedASTs f z, modifyContainedASTs f w)

instance
    (ASTContainer c t, ASTContainer d t, ASTContainer e t, ASTContainer g t, ASTContainer h t) => ASTContainer (c, d, e, g, h) t where
        containedASTs (x, y, z, w, a) = containedASTs x ++ containedASTs y ++ containedASTs z ++ containedASTs w ++ containedASTs a

        modifyContainedASTs f (x, y, z, w, a) = (modifyContainedASTs f x, modifyContainedASTs f y, modifyContainedASTs f z, modifyContainedASTs f w, modifyContainedASTs f  a)

-- Miscellaneous Instances
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

instance ASTContainer T.Text Expr where
    containedASTs _ = []
    modifyContainedASTs _ t = t

instance ASTContainer T.Text Type where
    containedASTs _ = []
    modifyContainedASTs _ t = t

instance ASTContainer Int Expr where
    containedASTs _ = []
    modifyContainedASTs _ t = t

instance ASTContainer Int Type where
    containedASTs _ = []
    modifyContainedASTs _ t = t


-- AlgDataTy
instance ASTContainer AlgDataTy Expr where
    containedASTs _ = []

    modifyContainedASTs _ a = a

instance ASTContainer AlgDataTy Type where
    containedASTs (DataTyCon ns dcs) = containedASTs ns ++ containedASTs dcs
    containedASTs (NewTyCon ns dcs r) = containedASTs ns ++ containedASTs dcs ++ containedASTs r
    containedASTs (TypeSynonym _ st) = containedASTs st

    modifyContainedASTs f (DataTyCon ns dcs) = DataTyCon (modifyContainedASTs f ns) (modifyContainedASTs f dcs)
    modifyContainedASTs f (NewTyCon ns dcs rt) = NewTyCon (modifyContainedASTs f ns) (modifyContainedASTs f dcs) (modifyContainedASTs f rt)
    modifyContainedASTs f (TypeSynonym is st) = TypeSynonym is (modifyContainedASTs f st)

instance ASTContainer AlgDataTy DataCon where
    containedASTs (DataTyCon _ dcs) = dcs
    containedASTs (NewTyCon _ dcs _) = [dcs]
    containedASTs (TypeSynonym _ _) = []

    modifyContainedASTs f (DataTyCon ns dcs) = DataTyCon ns (modifyContainedASTs f dcs)
    modifyContainedASTs f (NewTyCon ns dc rt) = NewTyCon ns (modifyContainedASTs f dc) rt
    modifyContainedASTs _ st@(TypeSynonym _ _) = st

instance (ASTContainer k t, ASTContainer v t, Eq k, Hashable k) => ASTContainer (UF.UFMap k v) t where
    containedASTs = containedASTs . UF.toList
    modifyContainedASTs f = UF.fromList . modifyContainedASTs f . UF.toList

-- ====== --
-- AST Helper functions
-- ====== --

-- | `replaceASTs old new container` returns `container` but with all occurences of `old` replaced with `new`.
replaceASTs :: (Eq e, ASTContainer c e) => e -> e -> c -> c
replaceASTs old new = modifyContainedASTs (replaceASTs' old new)

replaceASTs' :: (Eq e, AST e) => e -> e -> e -> e
replaceASTs' old new e = if e == old then new else modifyChildren (replaceASTs' old new) e