{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Internals.Language.ExprEnv
    ( ExprEnv
    , empty
    , singleton
    , null
    , size
    , member
    , lookup
    , primLookUp
    , insert
    , insertExprs
    , redirect
    , (!)
    , map
    , mapWithKey
    , filter
    , filterWithKey
    , keys
    , elems
    , toList
    , toExprList
    , fromExprList
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax

import Prelude hiding( filter
                     , lookup
                     , map
                     , null)
import Data.Either
import qualified Data.List as L
import qualified Data.Map as M

-- | From a user perspective, `ExprEnv`s are mappings from `Name` to
-- `Expr`s. however, because redirection pointers are included, this
-- complicates things. Instead, we use the `Either` type to separate
-- redirection and actual objects, so by using the supplied lookup functions,
-- the user should never be returned a redirection pointer from `ExecExprEnv`
-- lookups.
newtype ExprEnv = ExprEnv (M.Map Name (Either Name Expr))
                  deriving (Show, Eq, Read)

unwrapExprEnv :: ExprEnv -> M.Map Name (Either Name Expr)
unwrapExprEnv (ExprEnv env) = env

empty :: ExprEnv
empty = ExprEnv M.empty

singleton :: Name -> Expr -> ExprEnv
singleton n e = ExprEnv $ M.singleton n (Right e)

null :: ExprEnv -> Bool
null = M.null . unwrapExprEnv

size :: ExprEnv -> Int
size = M.size . unwrapExprEnv

member :: Name -> ExprEnv -> Bool
member n = M.member n . unwrapExprEnv

lookup :: Name -> ExprEnv -> Maybe Expr
lookup name (ExprEnv smap) = 
    case M.lookup name smap of
        Just (Left redir) -> lookup redir (ExprEnv smap)
        Just (Right expr) -> Just expr
        Nothing -> Nothing

primLookUp :: Primitive -> ExprEnv -> Expr
primLookUp p eenv = case occLookup (primStr p) (Just "GHC.Classes") eenv of
    Just e -> e
    Nothing -> error $ "Unrecognized prim"

occLookup :: String -> Maybe String -> ExprEnv -> Maybe Expr
occLookup n m = 
    fmap snd . L.find (\(Name n' m' _, _) -> n == n' && (m == m' || m' == Just "PrimDefs")) 
           . M.toList . M.map (\(Right e) -> e) . M.filter (isRight) . unwrapExprEnv

(!) :: ExprEnv -> Name -> Expr
(!) env@(ExprEnv env') n =
    case env' M.! n of
        Left n' -> env ! n'
        Right e -> e

insert :: Name -> Expr -> ExprEnv -> ExprEnv
insert n e = ExprEnv . M.insert n (Right e) . unwrapExprEnv

insertExprs :: [(Name, Expr)] -> ExprEnv -> ExprEnv
insertExprs kvs scope = foldr (uncurry insert) scope kvs

redirect :: Name -> Name -> ExprEnv -> ExprEnv
redirect n n' = ExprEnv . M.insert n (Left n') . unwrapExprEnv

map :: (Expr -> Expr) -> ExprEnv -> ExprEnv
map f = ExprEnv . M.map (either (Left) (Right . f)) . unwrapExprEnv

mapWithKey :: (Name -> Expr -> Expr) -> ExprEnv -> ExprEnv
mapWithKey f (ExprEnv env) = ExprEnv $ M.mapWithKey f' env
    where
        f' :: Name -> Either Name Expr -> Either Name Expr
        f' n (Right e) = Right $ f n e
        f' _ n = n

filter :: (Expr -> Bool) -> ExprEnv -> ExprEnv
filter p = filterWithKey (\_ -> p) 

filterWithKey :: (Name -> Expr -> Bool) -> ExprEnv -> ExprEnv
filterWithKey p env@(ExprEnv env') = ExprEnv $ M.filterWithKey p' env'
    where
        p' :: Name -> (Either Name Expr) -> Bool
        p' n (Left n') = p n (env ! n')
        p' n (Right e) = p n e

keys :: ExprEnv -> [Name]
keys = M.keys . unwrapExprEnv

elems :: ExprEnv -> [Expr]
elems = rights . M.elems . unwrapExprEnv

toList :: ExprEnv -> [(Name, Either Name Expr)]
toList = M.toList . unwrapExprEnv

-- | Creates a list of Name to Expr coorespondences
-- Looses information about names that are mapped to the same value
toExprList :: ExprEnv -> [(Name, Expr)]
toExprList env@(ExprEnv env') =
    M.toList
    . M.mapWithKey (\k _ -> env ! k) $ env'

fromExprList :: [(Name, Expr)] -> ExprEnv
fromExprList = ExprEnv . M.fromList . L.map (\(n, e) -> (n, Right e))

instance ASTContainer ExprEnv Expr where
    containedASTs = elems
    modifyContainedASTs f = map f

instance ASTContainer ExprEnv Type where
    containedASTs = containedASTs . elems
    modifyContainedASTs f = modifyContainedASTs f

instance Renamable ExprEnv where
    rename old new = ExprEnv . rename old new . unwrapExprEnv

