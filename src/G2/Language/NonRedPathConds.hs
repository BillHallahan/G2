{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, PatternSynonyms, ViewPatterns #-}

module G2.Language.NonRedPathConds ( NonRedPathConds
                                   , emptyNRPC
                                   , addNRPC
                                   , getNRPC
                                   , toListNRPC
                                   , pattern (:*>)) where

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax

import Data.Data (Data, Typeable)
import qualified Data.Foldable as F
import Data.Hashable
import Data.Sequence
import GHC.Generics (Generic)

newtype NonRedPathConds = NRPC (Seq (Expr, Expr)) deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable NonRedPathConds

emptyNRPC :: NonRedPathConds
emptyNRPC = NRPC Empty

addNRPC :: Expr -> Expr -> NonRedPathConds -> NonRedPathConds
addNRPC e1 e2 (NRPC nrpc) = NRPC (nrpc :|> (e1, e2))

getNRPC :: NonRedPathConds -> Maybe ((Expr, Expr), NonRedPathConds)
getNRPC (NRPC Empty) = Nothing
getNRPC (NRPC ((e1, e2) :<| nrpc)) = Just ((e1, e2), NRPC nrpc)

toListNRPC :: NonRedPathConds -> [(Expr, Expr)]
toListNRPC (NRPC nrpc) = F.toList nrpc

pattern (:*>) :: (Expr, Expr) -> NonRedPathConds -> NonRedPathConds
pattern e1_e2 :*> nrpc <- (getNRPC -> Just (e1_e2, nrpc))

instance ASTContainer NonRedPathConds Expr where
    containedASTs (NRPC nrpc) = containedASTs nrpc
    modifyContainedASTs f (NRPC nrpc) = NRPC $ modifyContainedASTs f nrpc

instance ASTContainer NonRedPathConds Type where
    containedASTs (NRPC nrpc) = containedASTs nrpc
    modifyContainedASTs f (NRPC nrpc) = NRPC $ modifyContainedASTs f nrpc

instance Named NonRedPathConds where
    names (NRPC nrpc) = names nrpc
    rename old new (NRPC nrpc) = NRPC (rename old new nrpc)
    renames hm (NRPC nrpc) = NRPC (renames hm nrpc)