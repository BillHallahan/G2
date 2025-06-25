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

data NRPC = NRPC { expr1 :: Expr, expr2 :: Expr } deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable NRPC

newtype NonRedPathConds = NRPCs (Seq NRPC) deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable NonRedPathConds

emptyNRPC :: NonRedPathConds
emptyNRPC = NRPCs Empty

addNRPC :: Expr -> Expr -> NonRedPathConds -> NonRedPathConds
addNRPC e1 e2 (NRPCs nrpc) = NRPCs (nrpc :|> NRPC { expr1 = e1, expr2 = e2 })

getNRPC :: NonRedPathConds -> Maybe ((Expr, Expr), NonRedPathConds)
getNRPC (NRPCs Empty) = Nothing
getNRPC (NRPCs (NRPC { expr1 = e1, expr2 = e2 } :<| nrpc)) = Just ((e1, e2), NRPCs nrpc)

toListNRPC :: NonRedPathConds -> [(Expr, Expr)]
toListNRPC (NRPCs nrpc) = map (\nrpc -> (expr1 nrpc, expr2 nrpc)) $ F.toList nrpc

pattern (:*>) :: (Expr, Expr) -> NonRedPathConds -> NonRedPathConds
pattern e1_e2 :*> nrpc <- (getNRPC -> Just (e1_e2, nrpc))

instance ASTContainer NRPC Expr where
    containedASTs (NRPC { expr1 = e1, expr2 = e2 }) = [e1, e2]
    modifyContainedASTs f (NRPC { expr1 = e1, expr2 = e2 }) = NRPC { expr1 = f e1, expr2 = f e2 }

instance ASTContainer NRPC Type where
    containedASTs (NRPC { expr1 = e1, expr2 = e2 }) = containedASTs e1 <> containedASTs e2
    modifyContainedASTs f (NRPC { expr1 = e1, expr2 = e2 }) =
        NRPC { expr1 = modifyContainedASTs f e1, expr2 = modifyContainedASTs f e2 }

instance Named NRPC where
    names (NRPC { expr1 = e1, expr2 = e2 }) = names e1 <> names e2
    rename old new (NRPC { expr1 = e1, expr2 = e2 }) = NRPC { expr1 = rename old new e1, expr2 = rename old new e2 }
    renames hm (NRPC { expr1 = e1, expr2 = e2 }) = NRPC { expr1 = renames hm e1, expr2 = renames hm e2 }

instance ASTContainer NonRedPathConds Expr where
    containedASTs (NRPCs nrpc) = containedASTs nrpc
    modifyContainedASTs f (NRPCs nrpc) = NRPCs $ modifyContainedASTs f nrpc

instance ASTContainer NonRedPathConds Type where
    containedASTs (NRPCs nrpc) = containedASTs nrpc
    modifyContainedASTs f (NRPCs nrpc) = NRPCs $ modifyContainedASTs f nrpc

instance Named NonRedPathConds where
    names (NRPCs nrpc) = names nrpc
    rename old new (NRPCs nrpc) = NRPCs (rename old new nrpc)
    renames hm (NRPCs nrpc) = NRPCs (renames hm nrpc)