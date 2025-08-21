{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{-# LANGUAGE LambdaCase, MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Language.ExprEnv
    ( ExprEnv
    , ConcOrSym (..)
    , EnvObj (..)

    , concOrSymToExpr

    , empty
    , singleton
    , fromList
    , null
    , size
    , toId
    , member
    , lookup
    , lookupConcOrSym
    , lookupEnvObj
    , deepLookup
    , deepLookupExpr
    , deepLookupConcOrSym
    , deepLookupVar
    , isSymbolic
    , occLookup
    , lookupNameMod
    , nameModMap
    , insert
    , insertSymbolic
    , insertExprs
    , difference
    , union
    , union'
    , unionWith
    , unionWithM
    , unionWithNameM
    , (!)
    , map
    , map'
    , mapConc
    , mapWithKey
    , mapWithKey'
    , mapConcWithKey
    , mapConcOrSym
    , mapConcOrSymWithKey
    , mapM
    , mapWithKeyM
    , filter
    , filterWithKey
    , filterConcOrSym
    , filterWithKey
    , filterConcOrSymWithKey
    , filterToSymbolic
    , getIdFromName
    , funcsOfType
    , keys
    , symbolicIds
    , elems
    , higherOrderExprs
    , toList
    , toExprList
    , fromExprList
    , fromExprMap
    , toHashMap
    ) where

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax
import G2.Language.Typing

import Prelude hiding( filter
                     , lookup
                     , map
                     , mapM
                     , null)
import qualified Prelude as Pre
import Data.Coerce
import Data.Data (Data, Typeable)
import Data.Hashable
import qualified Data.List as L
import qualified Data.HashMap.Lazy as M
import Data.Maybe
import qualified Data.Sequence as S
import qualified Data.Text as T
import qualified Data.Traversable as Trav
import GHC.Generics (Generic)
import qualified G2.Language.TyVarEnv as TV 

data ConcOrSym = Conc Expr
               | Sym Id
               deriving (Show)

concOrSymToExpr :: ConcOrSym -> Expr
concOrSymToExpr (Conc e) = e
concOrSymToExpr (Sym i) = Var i

-- From a user perspective, `ExprEnv`s are mappings from `Name` to
-- `Expr`s. however, certain names are symbolic.  This means they represent a symbolic variable
--  Nonsymbolic names map to an ExprObj, symbolic names to a SymObj.
 
data EnvObj = ExprObj Expr
            | SymbObj Id
            deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable EnvObj

-- | Maps `Name`s to `Expr`s.  Tracks `Type`s of symbolic variables. 
newtype ExprEnv = ExprEnv (M.HashMap Name EnvObj)
                  deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable ExprEnv

{-# INLINE unwrapExprEnv #-}
unwrapExprEnv :: ExprEnv -> M.HashMap Name EnvObj
unwrapExprEnv = coerce

toHashMap :: ExprEnv -> M.HashMap Name Expr
toHashMap eenv =
    M.map(\e -> case e of
                    ExprObj e' -> e'
                    SymbObj i -> Var i) . unwrapExprEnv $ eenv

-- | Constructs an empty `ExprEnv`
empty :: ExprEnv
empty = ExprEnv M.empty

-- | Constructs an `ExprEnv` with a single `Expr`.
singleton :: Name -> Expr -> ExprEnv
singleton n e = ExprEnv $ M.singleton n (ExprObj e)

-- | Constructs an `ExprEnv` from a list of `Name` and `Expr` pairs.
fromList :: [(Name, Expr)] -> ExprEnv
fromList = ExprEnv . M.fromList . Pre.map (\(n, e) -> (n, ExprObj e))

-- | Is the `ExprEnv` empty?
null :: ExprEnv -> Bool
null = M.null . unwrapExprEnv

-- | Returns the number of `Expr` in the `ExprEnv`.
size :: ExprEnv -> Int
size = M.size . unwrapExprEnv

-- | Is the given `Name` bound in the `ExprEnv`?
member :: Name -> ExprEnv -> Bool
member n = M.member n . unwrapExprEnv

toId :: TV.TyVarEnv -> Name -> ExprEnv -> Maybe Id
toId tv n eenv = fmap (Id n . typeOf tv) (lookup n eenv)

-- | Lookup the `Expr` with the given `Name`.
-- Returns `Nothing` if the `Name` is not in the `ExprEnv`.
lookup :: Name -> ExprEnv -> Maybe Expr
lookup n (ExprEnv smap) = 
    case M.lookup n smap of
        Just (ExprObj expr) -> Just expr
        Just (SymbObj i) -> Just $ Var i
        Nothing -> Nothing

lookupConcOrSym :: Name -> ExprEnv -> Maybe ConcOrSym
lookupConcOrSym  n (ExprEnv smap) = 
    case M.lookup n smap of
        Just (ExprObj expr) -> Just $ Conc expr
        Just (SymbObj i) -> Just $ Sym i
        Nothing -> Nothing

lookupEnvObj :: Name -> ExprEnv -> Maybe EnvObj
lookupEnvObj n = M.lookup n . unwrapExprEnv

-- | Lookup the `Expr` with the given `Name`.
-- If the name is bound to a @Var@, recursively searches that @Vars@ name.
-- Returns `Nothing` if the `Name` is not in the `ExprEnv`.
deepLookup :: Name -> ExprEnv -> Maybe Expr
deepLookup n eenv =
    case lookupConcOrSym n eenv of
        Just (Conc (Var (Id n' _))) -> deepLookup n' eenv
        Just (Conc r) -> Just r
        Just (Sym r) -> Just (Var r)
        Nothing -> Nothing

-- | Apply `deepLookup` if passed a `Var`.  Otherwise, just return the passed `Expr`.
deepLookupExpr :: Expr -> ExprEnv -> Expr
deepLookupExpr v@(Var (Id n _)) eenv = fromMaybe v (deepLookup n eenv)
deepLookupExpr e _  = e

deepLookupConcOrSym :: Name -> ExprEnv -> Maybe ConcOrSym
deepLookupConcOrSym n eenv =
    case lookupConcOrSym n eenv of
        Just (Conc (Var (Id n' _))) -> deepLookupConcOrSym n' eenv
        Just c@(Conc r) -> Just c
        Just s@(Sym r) -> Just s
        Nothing -> Nothing

-- | Find the deepest buried Var Id from the given Name
deepLookupVar :: TV.TyVarEnv -> Name -> ExprEnv -> Maybe Id
deepLookupVar tv n eenv = go (toId tv n eenv) n
    where
        go lst f = 
            case lookupConcOrSym f eenv of
                Just (Conc (Var i@(Id f' _))) -> go (Just i) f'
                Just (Conc r) -> lst
                Just (Sym r) -> Just r
                Nothing -> Nothing

-- | Checks if the given `Name` belongs to a symbolic variable.
isSymbolic :: Name -> ExprEnv -> Bool
isSymbolic n eenv =
    case lookupConcOrSym n eenv of
        Just (Sym _) -> True
        _ -> False

occLookup :: TV.TyVarEnv -> T.Text -> Maybe T.Text -> ExprEnv -> Maybe Expr
occLookup tv n m (ExprEnv eenv) = 
    let ex = L.find (\(Name n' m' _ _, _) -> n == n' && (m == m' || m' == Just "PrimDefs")) -- TODO: The PrimDefs exception should not be here! 
           . M.toList . M.mapMaybe (\case (ExprObj e) -> Just e; _ -> Nothing) $ eenv
    in
    fmap (\(n', e) -> Var $ Id n' (typeOf tv e)) ex

lookupNameMod :: T.Text -> Maybe T.Text -> ExprEnv -> Maybe (Name, Expr)
lookupNameMod ns ms =
    listToMaybe . L.filter (\(Name n m _ _, _) -> ns == n && ms == m) . toExprList

nameModMap :: ExprEnv -> M.HashMap (T.Text, Maybe T.Text) (Name, Expr)
nameModMap = M.fromList . L.map (\(n@(Name n' m _ _), e) -> ((n', m), (n, e))) . toExprList

-- | Looks  up a `Name` in the `ExprEnv`.  Crashes if the `Name` is not found.
(!) :: ExprEnv -> Name -> Expr
(!) env@(ExprEnv env') n =
    case M.lookup n env' of
        Just (ExprObj e) -> e
        Just (SymbObj i) -> Var i
        Nothing -> error $ "ExprEnv.!: Given key is not an element of the expr env" ++ show n

-- | Inserts a new `Expr` into the `ExorEnv`, at the given `Name`.
-- If the `Name` already exists in the `ExprEnv`, the `Expr` is replaced.
insert :: Name -> Expr -> ExprEnv -> ExprEnv
insert n e = ExprEnv . M.insert n (ExprObj e) . unwrapExprEnv

insertSymbolic :: Id -> ExprEnv -> ExprEnv
insertSymbolic i = ExprEnv. M.insert (idName i) (SymbObj i) . unwrapExprEnv

insertExprs :: [(Name, Expr)] -> ExprEnv -> ExprEnv
insertExprs kvs scope = foldr (uncurry insert) scope kvs

difference :: ExprEnv -> ExprEnv -> ExprEnv
difference (ExprEnv m1) (ExprEnv m2) =
    ExprEnv $ M.difference m1 m2

-- | Get the union of two `ExprEnv`.  If names overlap, keep the mapping in the left `ExprEnv`.
union :: ExprEnv -> ExprEnv -> ExprEnv
union (ExprEnv eenv) (ExprEnv eenv') = ExprEnv $ eenv `M.union` eenv'

union' :: M.HashMap Name Expr -> ExprEnv -> ExprEnv
union' m (ExprEnv eenv) = ExprEnv (M.map ExprObj m `M.union` eenv)

-- | Get the union of two `ExprEnv`.  If names overlap, use the passed function to get an `EnvObj`.
unionWith :: (EnvObj -> EnvObj -> EnvObj) -> ExprEnv -> ExprEnv -> ExprEnv
unionWith f (ExprEnv m1) (ExprEnv m2) =
    ExprEnv $ M.unionWith f m1 m2

unionWithM :: Monad m => (EnvObj -> EnvObj -> m EnvObj) -> ExprEnv -> ExprEnv -> m ExprEnv
unionWithM f (ExprEnv m1) (ExprEnv m2) =
    return . ExprEnv =<< (Trav.sequence $ M.unionWith (\x y -> do
                                                            x' <- x
                                                            y' <- y
                                                            f x' y') 
                                                      (M.map return m1)
                                                      (M.map return m2))

unionWithNameM :: Monad m => (Name -> EnvObj -> EnvObj -> m EnvObj) -> ExprEnv -> ExprEnv -> m ExprEnv
unionWithNameM f (ExprEnv m1) (ExprEnv m2) =
    return . ExprEnv =<< (Trav.sequence $ M.unionWithKey (\n x y -> do
                                                                    x' <- x
                                                                    y' <- y
                                                                    f n x' y') 
                                                         (M.map return m1)
                                                         (M.map return m2))

-- | Map a function over all `Expr` in the `ExprEnv`.
-- Will not replace symbolic variables with non-symbolic values,
-- but will rename symbolic values if the passed function
-- returns a `Var`.
map :: (Expr -> Expr) -> ExprEnv -> ExprEnv
map f = mapWithKey (\_ -> f)

-- | Maps a function with an arbitrary return type over all `Expr` in the `ExprEnv`, to get a `Data.HashMap`.
map' :: (Expr -> a) -> ExprEnv -> M.HashMap Name a
map' f = mapWithKey' (\_ -> f)

mapConc :: (Expr -> Expr) -> ExprEnv -> ExprEnv
mapConc f = mapConcWithKey (\_ -> f)

-- | Map a function over all `Expr` in the `ExprEnv`, with access to the `Name`.
-- Will not replace symbolic variables with non-symbolic values,
-- but will rename symbolic values.
mapWithKey :: (Name -> Expr -> Expr) -> ExprEnv -> ExprEnv
mapWithKey f (ExprEnv env) = ExprEnv $ M.mapWithKey f' env
    where
        f' :: Name -> EnvObj -> EnvObj
        f' n (ExprObj e) = ExprObj $ f n e
        f' n s@(SymbObj i) = 
            case f n (Var i) of
                Var i' -> SymbObj i'
                _ -> s
        f' _ n = n

mapWithKey' :: (Name -> Expr -> a) -> ExprEnv -> M.HashMap Name a
mapWithKey' f = M.mapWithKey f . toExprMap

mapConcWithKey :: (Name -> Expr -> Expr) -> ExprEnv -> ExprEnv
mapConcWithKey f (ExprEnv env) = ExprEnv $ M.mapWithKey f' env
    where
        f' :: Name -> EnvObj -> EnvObj
        f' n (ExprObj e) = ExprObj $ f n e
        f' _ s@(SymbObj _) = s
        f' _ n = n

mapConcOrSym :: (ConcOrSym -> ConcOrSym) -> ExprEnv -> ExprEnv
mapConcOrSym f = mapConcOrSymWithKey (\_ -> f)

mapConcOrSymWithKey :: (Name -> ConcOrSym -> ConcOrSym) -> ExprEnv -> ExprEnv
mapConcOrSymWithKey f (ExprEnv env) = ExprEnv $ M.mapWithKey f' env
    where
        g :: ConcOrSym -> EnvObj
        g (Conc e) = ExprObj e
        g (Sym i) = SymbObj i
        f' :: Name -> EnvObj -> EnvObj
        f' n (ExprObj e) = g $ f n $ Conc e
        f' n (SymbObj i) = g $ f n $ Sym i
        f' _ e = e

mapM :: Monad m => (Expr -> m Expr) -> ExprEnv -> m ExprEnv
mapM f eenv = return . ExprEnv =<< Pre.mapM f' (unwrapExprEnv eenv)
    where
        f' (ExprObj e) = return . ExprObj =<< f e
        f' s@(SymbObj i) = do
            e' <- f (Var i)
            case e' of
                Var i' -> return $ SymbObj i'
                _ -> return s
        f' n = return n


mapWithKeyM :: Monad m => (Name -> Expr -> m Expr) -> ExprEnv -> m ExprEnv
mapWithKeyM f eenv = return . ExprEnv . M.fromList =<< Pre.mapM (uncurry f') (toList eenv)
    where
        f' n (ExprObj e) = return . (n,) . ExprObj =<< f n e
        f' n s@(SymbObj i) = do
            e' <- f n (Var i)
            case e' of
                Var i' -> return $ (n, SymbObj i')
                _ -> return (n, s)
        f' n e = return (n, e)

filter :: (Expr -> Bool) -> ExprEnv -> ExprEnv
filter p = filterWithKey (\_ -> p) 

filterWithKey :: (Name -> Expr -> Bool) -> ExprEnv -> ExprEnv
filterWithKey p env@(ExprEnv env') = ExprEnv $ M.filterWithKey p' env'
    where
        p' :: Name -> EnvObj -> Bool
        p' n (ExprObj e) = p n e
        p' n (SymbObj i) = p n (Var i)

filterConcOrSym :: (ConcOrSym -> Bool) -> ExprEnv -> ExprEnv
filterConcOrSym p = filterConcOrSymWithKey (\_ -> p) 

filterConcOrSymWithKey :: (Name -> ConcOrSym -> Bool) -> ExprEnv -> ExprEnv
filterConcOrSymWithKey p env@(ExprEnv env') = ExprEnv $ M.filterWithKey p' env'
    where
        p' :: Name -> EnvObj -> Bool
        p' n (ExprObj e) = p n (Conc e)
        p' n (SymbObj i) = p n (Sym i)

-- | Returns a new `ExprEnv`, which contains only the symbolic values.
filterToSymbolic :: ExprEnv -> ExprEnv
filterToSymbolic = ExprEnv . M.filter (\e -> case e of
                                                SymbObj _ -> True
                                                _ -> False) . unwrapExprEnv

-- | Returns the names of all expressions with the given type in the expression environment
funcsOfType :: TV.TyVarEnv -> Type -> ExprEnv -> [Name]
funcsOfType tv t = keys . filter (\e -> t == typeOf tv e)

keys :: ExprEnv -> [Name]
keys = M.keys . unwrapExprEnv

symbolicIds :: ExprEnv -> [Id]
symbolicIds = mapMaybe (\e -> case e of
                                SymbObj i ->  Just i
                                _ -> Nothing) . M.elems . unwrapExprEnv

-- | Returns all `Expr`@s@ in the `ExprEnv`
elems :: ExprEnv -> [Expr]
elems = exprObjs . M.elems . unwrapExprEnv

-- | Returns a list of all argument function types 
higherOrderExprs :: TV.TyVarEnv -> ExprEnv -> [Type]
higherOrderExprs tv eenv = concatMap (higherOrderFuncs . typeOf tv ) (elems eenv)

toList :: ExprEnv -> [(Name, EnvObj)]
toList = M.toList . unwrapExprEnv

-- | Creates a list of Name to Expr coorespondences
-- Loses information about names that are mapped to the same value
toExprList :: ExprEnv -> [(Name, Expr)]
toExprList env@(ExprEnv env') =
    M.toList
    . M.mapWithKey (\k _ -> env ! k) $ env'

fromExprList :: [(Name, Expr)] -> ExprEnv
fromExprList = ExprEnv . M.fromList . L.map (\(n, e) -> (n, ExprObj e))

fromExprMap :: M.HashMap Name Expr -> ExprEnv
fromExprMap = ExprEnv . M.map ExprObj

toExprMap :: ExprEnv -> M.HashMap Name Expr
toExprMap env = M.mapWithKey (\k _ -> env ! k) $ unwrapExprEnv env

getIdFromName :: ExprEnv -> Name -> Maybe Id
getIdFromName eenv name = 
    case (lookup name eenv) of 
        Just (Var i) -> Just i       
        _ -> Nothing

-- Symbolic objects will be returned by calls to eval functions, however
-- calling AST modify functions on the expressions in an ExprEnv will have
-- no effect on contained symbolic objects, unless the returned type is also a Var.
-- This is to mantain the invariant that a symbolic object is just a Var
instance ASTContainer ExprEnv Expr where
    containedASTs = elems
    modifyContainedASTs f = map f

instance ASTContainer ExprEnv Type where
    containedASTs = containedASTs . elems
    modifyContainedASTs f = map (modifyContainedASTs f)

instance ASTContainer EnvObj Expr where
    containedASTs (ExprObj e) = [e]
    containedASTs (SymbObj i) = [Var i]

    modifyContainedASTs f (ExprObj e) = ExprObj (f e)
    modifyContainedASTs f s@(SymbObj i) =
        case f (Var i) of
            (Var i') -> SymbObj i'
            _ -> s
    modifyContainedASTs _ r = r

instance ASTContainer EnvObj Type where
    containedASTs (ExprObj e) = containedASTs e
    containedASTs (SymbObj i) = containedASTs i

    modifyContainedASTs f (ExprObj e) = ExprObj (modifyContainedASTs f e)
    modifyContainedASTs f (SymbObj i) = SymbObj (modifyContainedASTs f i)
    modifyContainedASTs _ r = r

instance Named ExprEnv where
    names (ExprEnv eenv) = names (M.keys eenv) <> names eenv

    rename old new =
        ExprEnv 
        . M.fromList
        . rename old new
        . M.toList
        . unwrapExprEnv

    renames hm =
        ExprEnv
        . M.fromList
        . renames hm
        . M.toList
        . unwrapExprEnv

instance Named EnvObj where
    names (ExprObj e) = names e
    names (SymbObj s) = names s

    rename old new (ExprObj e) = ExprObj $ rename old new e
    rename old new (SymbObj s) = SymbObj $ rename old new s

    renames hm (ExprObj e) = ExprObj $ renames hm e
    renames hm (SymbObj s) = SymbObj $ renames hm s

-- Helpers for EnvObjs

exprObjs :: [EnvObj]  -> [Expr]
exprObjs [] = []
exprObjs (ExprObj e:xs) = e:exprObjs xs
exprObjs (SymbObj i:xs) = Var i:exprObjs xs