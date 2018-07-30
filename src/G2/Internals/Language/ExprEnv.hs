{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Language.ExprEnv
    ( ExprEnv
    , empty
    , singleton
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
    , insertPreserving
    , insertExprs
    , redirect
    , union
    , (!)
    , map
    , map'
    , mapWithKey
    , mapWithKey'
    , mapKeys
    , filter
    , filterWithKey
    , filterToSymbolic
    , funcsOfType
    , keys
    , symbolicKeys
    , elems
    , higherOrderExprs
    , toList
    , toExprList
    , fromExprList
    , isRedirect
    , isRoot
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import G2.Internals.Language.Typing

import Prelude hiding( filter
                     , lookup
                     , map
                     , null)
import Data.Coerce
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

-- | From a user perspective, `ExprEnv`s are mappings from `Name` to
-- `Expr`s. however, there are two complications:
--  1) Redirection pointers can map two names to the same expr
--  2) Certain names are symbolic.  This means they represent a symbolic variable
--     Nonsymbolic names map to an ExprObj, symbolic names to a SymObj.
 
data EnvObj = ExprObj Expr
            | RedirObj Name
            | SymbObj Id
            deriving (Show, Eq, Read)

newtype ExprEnv = ExprEnv (M.Map Name EnvObj)
                  deriving (Show, Eq, Read)

unwrapExprEnv :: ExprEnv -> M.Map Name EnvObj
unwrapExprEnv = coerce

empty :: ExprEnv
empty = ExprEnv M.empty

singleton :: Name -> Expr -> ExprEnv
singleton n e = ExprEnv $ M.singleton n (ExprObj e)

null :: ExprEnv -> Bool
null = M.null . unwrapExprEnv

size :: ExprEnv -> Int
size = M.size . unwrapExprEnv

member :: Name -> ExprEnv -> Bool
member n = M.member n . unwrapExprEnv

lookup :: Name -> ExprEnv -> Maybe Expr
lookup n (ExprEnv smap) = 
    case M.lookup n smap of
        Just (ExprObj expr) -> Just expr
        Just (RedirObj redir) -> lookup redir (ExprEnv smap)
        Just (SymbObj i) -> Just $ Var i
        Nothing -> Nothing

deepLookup :: Name -> ExprEnv -> Maybe Expr
deepLookup n eenv =
    case lookup n eenv of
        Just (Var (Id n' _)) -> lookup n' eenv
        r -> r

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

(!) :: ExprEnv -> Name -> Expr
(!) env@(ExprEnv env') n =
    case M.lookup n env' of
        Just (RedirObj n') -> env ! n'
        Just (ExprObj e) -> e
        Just (SymbObj i) -> Var i
        Nothing -> error $ "ExprEnv.!: Given key is not an element of the expr env" ++ show n

insert :: Name -> Expr -> ExprEnv -> ExprEnv
insert n e = ExprEnv . M.insert n (ExprObj e) . unwrapExprEnv

insertSymbolic :: Name -> Id -> ExprEnv -> ExprEnv
insertSymbolic n i = ExprEnv. M.insert n (SymbObj i) . unwrapExprEnv

-- Inserts into the expr env, preserving the EnvObj type
-- Will make no changes if this is not possible
insertPreserving :: Name -> Expr -> ExprEnv -> ExprEnv
insertPreserving n e eenv
    | isSymbolic n eenv
    , (Var i) <- e =
        insertSymbolic n i eenv
    | isSymbolic n eenv || isRedirect n eenv =
        eenv
    | otherwise = insert n e eenv


insertExprs :: [(Name, Expr)] -> ExprEnv -> ExprEnv
insertExprs kvs scope = foldr (uncurry insert) scope kvs

redirect :: Name -> Name -> ExprEnv -> ExprEnv
redirect n n' = ExprEnv . M.insert n (RedirObj n') . unwrapExprEnv

union :: ExprEnv -> ExprEnv -> ExprEnv
union (ExprEnv eenv) (ExprEnv eenv') = ExprEnv $ eenv `M.union` eenv'

map :: (Expr -> Expr) -> ExprEnv -> ExprEnv
map f = mapWithKey (\_ -> f)

map' :: (Expr -> a) -> ExprEnv -> M.Map Name a
map' f = mapWithKey' (\_ -> f)

-- Maps (SymbObj v) iff f v is also a Var
-- Does not affect redirects
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

filter :: (Expr -> Bool) -> ExprEnv -> ExprEnv
filter p = filterWithKey (\_ -> p) 

filterWithKey :: (Name -> Expr -> Bool) -> ExprEnv -> ExprEnv
filterWithKey p env@(ExprEnv env') = ExprEnv $ M.filterWithKey p' env'
    where
        p' :: Name -> EnvObj -> Bool
        p' n (RedirObj n') = p n (env ! n')
        p' n (ExprObj e) = p n e
        p' n (SymbObj i) = p n (Var i)

filterToSymbolic :: ExprEnv -> ExprEnv
filterToSymbolic eenv = filterWithKey (\n _ -> isSymbolic n eenv) eenv

-- | funcsOfType
-- Returns the names of all expressions with the given type in the expression environment
funcsOfType :: Type -> ExprEnv -> [Name]
funcsOfType t = keys . filter (\e -> t == typeOf e)

keys :: ExprEnv -> [Name]
keys = M.keys . unwrapExprEnv

symbolicKeys :: ExprEnv -> [Name]
symbolicKeys eenv = M.keys . unwrapExprEnv . filterWithKey (\n _ -> isSymbolic n eenv) $ eenv

--TODO
elems :: ExprEnv -> [Expr]
elems = exprObjs . M.elems . unwrapExprEnv

-- | higherOrderExprs
-- Returns a list of all argument function types 
higherOrderExprs :: ExprEnv -> [Type]
higherOrderExprs = concatMap (higherOrderFuncs) . elems


toList :: ExprEnv -> [(Name, EnvObj)]
toList = M.toList . unwrapExprEnv

-- | Creates a list of Name to Expr coorespondences
-- Looses information about names that are mapped to the same value
toExprList :: ExprEnv -> [(Name, Expr)]
toExprList env@(ExprEnv env') =
    M.toList
    . M.mapWithKey (\k _ -> env ! k) $ env'

fromExprList :: [(Name, Expr)] -> ExprEnv
fromExprList = ExprEnv . M.fromList . L.map (\(n, e) -> (n, ExprObj e))

toExprMap :: ExprEnv -> M.Map Name Expr
toExprMap env = M.mapWithKey (\k _ -> env ! k) $ unwrapExprEnv env

-- Returns True iff n is a redirect in the ExprEnv
isRedirect :: Name -> ExprEnv -> Bool
isRedirect n (ExprEnv eenv) =
    case M.lookup n eenv of
        Just (RedirObj _) -> True
        _ -> False

isRoot :: Name -> ExprEnv -> Bool
isRoot n (ExprEnv eenv) =
    case M.lookup n eenv of
        Just (ExprObj _) -> True
        _ -> False

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
