{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Language.ExprEnv
    ( ExprEnv
    , empty
    , singleton
    , fromList
    , null
    , size
    , member
    , lookup
    , deepLookup
    , isSymbolic
    , occLookup
    , lookupNameMod
    , insert
    , insertSymbolic
    , insertExprs
    , redirect
    , union
    , (!)
    , map
    , map'
    , mapWithKey
    , mapWithKey'
    , mapKeys
    , mapM
    , mapWithKeyM
    , filter
    , filterWithKey
    , filterToSymbolic
    , getIdFromName
    , funcsOfType
    , keys
    , symbolicKeys
    , elems
    , higherOrderExprs
    , toList
    , toExprList
    , fromExprList
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
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

-- From a user perspective, `ExprEnv`s are mappings from `Name` to
-- `Expr`s. however, there are two complications:
--   1) Redirection pointers can map two names to the same expr
--   2) Certain names are symbolic.  This means they represent a symbolic variable
--      Nonsymbolic names map to an ExprObj, symbolic names to a SymObj.
 
data EnvObj = ExprObj Expr
            | RedirObj Name
            | SymbObj Id
            deriving (Show, Eq, Read, Typeable, Data)

newtype ExprEnv = ExprEnv (M.Map Name EnvObj)
                  deriving (Show, Eq, Read, Typeable, Data)

unwrapExprEnv :: ExprEnv -> M.Map Name EnvObj
unwrapExprEnv = coerce

-- | Constructs an empty `ExprEnv`
empty :: ExprEnv
empty = ExprEnv M.empty

-- | Constructs an `ExprEnv` with a single `Expr`.
singleton :: Name -> Expr -> ExprEnv
singleton n e = ExprEnv $ M.singleton n (ExprObj e)

-- | Constructs an `ExprEnv` from a list of `Name` and `Expr` pairs.
fromList :: [(Name, Expr)] -> ExprEnv
fromList = ExprEnv . M.fromList . Pre.map (\(n, e) -> (n, ExprObj e))

-- Is the `ExprEnv` empty?
null :: ExprEnv -> Bool
null = M.null . unwrapExprEnv

-- | Returns the number of `Expr` in the `ExprEnv`.
size :: ExprEnv -> Int
size = M.size . unwrapExprEnv

-- | Is the given `Name` bound in the `ExprEnv`?
member :: Name -> ExprEnv -> Bool
member n = M.member n . unwrapExprEnv

-- | Lookup the `Expr` with the given `Name`.
-- Returns `Nothing` if the `Name` is not in the `ExprEnv`.
lookup :: Name -> ExprEnv -> Maybe Expr
lookup n (ExprEnv smap) = 
    case M.lookup n smap of
        Just (ExprObj expr) -> Just expr
        Just (RedirObj redir) -> lookup redir (ExprEnv smap)
        Just (SymbObj i) -> Just $ Var i
        Nothing -> Nothing

-- | Lookup the `Expr` with the given `Name`.
-- If the name is bound to a @Var@, recursively searches that @Vars@ name.
-- Returns `Nothing` if the `Name` is not in the `ExprEnv`.
deepLookup :: Name -> ExprEnv -> Maybe Expr
deepLookup n eenv =
    case lookup n eenv of
        Just (Var (Id n' _)) -> lookup n' eenv
        r -> r

-- | Checks if the given `Name` belongs to a symbolic variable.
isSymbolic :: Name -> ExprEnv -> Bool
isSymbolic n (ExprEnv eenv') =
    case M.lookup n eenv' of
        Just (SymbObj _) -> True
        _ -> False

-- TODO -- This seems kinda too much like a special case to be here...
occLookup :: T.Text -> Maybe T.Text -> ExprEnv -> Maybe Expr
occLookup n m (ExprEnv eenv) = 
    let ex = L.find (\(Name n' m' _ _, _) -> n == n' && (m == m' || m' == Just "PrimDefs")) -- TODO: The PrimDefs exception should not be here! 
           . M.toList . M.map (\(ExprObj e) -> e) . M.filter (isExprObj) $ eenv
    in
    fmap (\(n', e) -> Var $ Id n' (typeOf e)) ex

lookupNameMod :: T.Text -> Maybe T.Text -> ExprEnv -> Maybe (Name, Expr)
lookupNameMod ns ms =
    listToMaybe . L.filter (\(Name n m _ _, _) -> ns == n && ms == m) . toExprList

-- | Looks  up a `Name` in the `ExprEnv`.  Crashes if the `Name` is not found.
(!) :: ExprEnv -> Name -> Expr
(!) env@(ExprEnv env') n =
    case M.lookup n env' of
        Just (RedirObj n') -> env ! n'
        Just (ExprObj e) -> e
        Just (SymbObj i) -> Var i
        Nothing -> error $ "ExprEnv.!: Given key is not an element of the expr env" ++ show n

-- | Inserts a new `Expr` into the `ExorEnv`, at the given `Name`.
-- If the `Name` already exists in the `ExprEnv`, the `Expr` is replaced.
insert :: Name -> Expr -> ExprEnv -> ExprEnv
insert n e = ExprEnv . M.insert n (ExprObj e) . unwrapExprEnv

insertSymbolic :: Name -> Id -> ExprEnv -> ExprEnv
insertSymbolic n i = ExprEnv. M.insert n (SymbObj i) . unwrapExprEnv

insertExprs :: [(Name, Expr)] -> ExprEnv -> ExprEnv
insertExprs kvs scope = foldr (uncurry insert) scope kvs

-- | Maps the two `Name`@s@ so that they point to the same value
redirect :: Name -> Name -> ExprEnv -> ExprEnv
redirect n n' = ExprEnv . M.insert n (RedirObj n') . unwrapExprEnv

union :: ExprEnv -> ExprEnv -> ExprEnv
union (ExprEnv eenv) (ExprEnv eenv') = ExprEnv $ eenv `M.union` eenv'

-- | Map a function over all `Expr` in the `ExprEnv`.
-- Will not replace symbolic variables with non-symbolic values,
-- but will rename symbolic values.
map :: (Expr -> Expr) -> ExprEnv -> ExprEnv
map f = mapWithKey (\_ -> f)

-- | Maps a function with an arbitrary return type over all `Expr` in the `ExprEnv`, to get a `Data.Map`.
map' :: (Expr -> a) -> ExprEnv -> M.Map Name a
map' f = mapWithKey' (\_ -> f)

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

mapWithKey' :: (Name -> Expr -> a) -> ExprEnv -> M.Map Name a
mapWithKey' f = M.mapWithKey f . toExprMap

mapKeys :: (Name -> Name) -> ExprEnv -> ExprEnv
mapKeys f = coerce . M.mapKeys f . unwrapExprEnv

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
        p' n (RedirObj n') = p n (env ! n')
        p' n (ExprObj e) = p n e
        p' n (SymbObj i) = p n (Var i)

-- | Returns a new `ExprEnv`, which contains only the symbolic values.
filterToSymbolic :: ExprEnv -> ExprEnv
filterToSymbolic eenv = filterWithKey (\n _ -> isSymbolic n eenv) eenv

-- | Returns the names of all expressions with the given type in the expression environment
funcsOfType :: Type -> ExprEnv -> [Name]
funcsOfType t = keys . filter (\e -> t == typeOf e)

keys :: ExprEnv -> [Name]
keys = M.keys . unwrapExprEnv

symbolicKeys :: ExprEnv -> [Name]
symbolicKeys eenv = M.keys . unwrapExprEnv . filterWithKey (\n _ -> isSymbolic n eenv) $ eenv

-- | Returns all `Expr`@s@ in the `ExprEnv`
elems :: ExprEnv -> [Expr]
elems = exprObjs . M.elems . unwrapExprEnv

-- | Returns a list of all argument function types 
higherOrderExprs :: ExprEnv -> [Type]
higherOrderExprs = concatMap (higherOrderFuncs) . elems

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

toExprMap :: ExprEnv -> M.Map Name Expr
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
    containedASTs (RedirObj _) = []
    containedASTs (SymbObj i) = [Var i]

    modifyContainedASTs f (ExprObj e) = ExprObj (f e)
    modifyContainedASTs f s@(SymbObj i) =
        case f (Var i) of
            (Var i') -> SymbObj i'
            _ -> s
    modifyContainedASTs _ r = r

instance ASTContainer EnvObj Type where
    containedASTs (ExprObj e) = containedASTs e
    containedASTs (RedirObj _) = []
    containedASTs (SymbObj i) = containedASTs i

    modifyContainedASTs f (ExprObj e) = ExprObj (modifyContainedASTs f e)
    modifyContainedASTs f (SymbObj i) = SymbObj (modifyContainedASTs f i)
    modifyContainedASTs _ r = r

instance Named ExprEnv where
    names (ExprEnv eenv) = names (M.keys eenv) ++ names eenv

    rename old new =
        ExprEnv 
        . M.mapKeys (\k -> if k == old then new else k)
        . rename old new
        . unwrapExprEnv

    renames hm =
        ExprEnv
        . M.mapKeys (renames hm)
        . renames hm
        . unwrapExprEnv

instance Named EnvObj where
    names (ExprObj e) = names e
    names (RedirObj r) = [r]
    names (SymbObj s) = names s

    rename old new (ExprObj e) = ExprObj $ rename old new e
    rename old new (RedirObj r) = RedirObj $ rename old new r
    rename old new (SymbObj s) = SymbObj $ rename old new s

    renames hm (ExprObj e) = ExprObj $ renames hm e
    renames hm (RedirObj r) = RedirObj $ renames hm r
    renames hm (SymbObj s) = SymbObj $ renames hm s

-- Helpers for EnvObjs

isExprObj :: EnvObj -> Bool
isExprObj (ExprObj _) = True
isExprObj _ = False

exprObjs :: [EnvObj]  -> [Expr]
exprObjs [] = []
exprObjs (ExprObj e:xs) = e:exprObjs xs
exprObjs (SymbObj i:xs) = Var i:exprObjs xs
exprObjs (_:xs) = exprObjs xs
