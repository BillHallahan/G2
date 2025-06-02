{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module G2.Language.Stack
    ( Stack
    , empty
    , null
    , push
    , pop
    , toList
    , filter) where

import Prelude hiding (null, filter)
import GHC.Generics (Generic)
import Data.Data (Data, Typeable)
import Data.Hashable
import qualified Data.List as L

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax

newtype Stack a = Stack [a] deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable a => Hashable (Stack a)

-- | Get an empty `Stack`.
empty :: Stack a
empty = Stack []

-- | Is the `Stack` empty?
null :: Stack a -> Bool
null = L.null . toList

-- | Push a value onto the `Stack`.
push :: a -> Stack a -> Stack a
push x (Stack xs) = Stack (x : xs)

-- | Pop a value from the `Stack`, should it exist.
pop :: Stack a -> Maybe (a, Stack a)
pop (Stack []) = Nothing
pop (Stack (x:xs)) = Just (x, Stack xs)

-- | Convert a `Stack` to a list.
toList :: Stack a -> [a]
toList (Stack xs) = xs

filter :: (a -> Bool) -> Stack a -> Stack a
filter p (Stack stck) = Stack (L.filter p stck)

instance ASTContainer a Expr => ASTContainer (Stack a) Expr where
    containedASTs (Stack s) = containedASTs s
    modifyContainedASTs f (Stack s) = Stack $ modifyContainedASTs f s

instance ASTContainer a Type => ASTContainer (Stack a) Type where
    containedASTs (Stack s) = containedASTs s
    modifyContainedASTs f (Stack s) = Stack $ modifyContainedASTs f s

instance Named a => Named (Stack a) where
    names (Stack s) = names s
    rename old new (Stack s) = Stack $ rename old new s
    renames hm (Stack s) = Stack $ renames hm s
