{-# LANGUAGE BangPatterns, DeriveDataTypeable, DeriveGeneric, LambdaCase,  MultiParamTypeClasses
, OverloadedStrings, PatternSynonyms, ViewPatterns #-}

module G2.Language.NonRedPathConds ( NonRedPathConds
                                   , NRPC
                                   , emptyNRPC
                                   , addNRPC
                                   , getNRPC
                                   , nullNRPC
                                   , toListNRPC
                                   , minIndexNRPC
                                   , maxIndexNRPC
                                   , allIndexesNRPC
                                   , pattern (:*>)
                                   , toListInternalNRPC) where

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax

import Data.Data (Data, Typeable)
import qualified Data.Foldable as F
import Data.Hashable
import qualified Data.HashSet as HS
import Data.Maybe
import Data.Sequence as Seq
import GHC.Generics (Generic)

data NRPC = NRPC { nrpc_index :: !Int, expr1 :: Expr, expr2 :: Expr }
          | Rotate deriving (Show, Eq, Read, Generic, Typeable, Data)

isNRPC :: NRPC -> Bool
isNRPC NRPC {} = True
isNRPC Rotate = False

nrpcIndex :: NRPC -> Maybe Int
nrpcIndex (NRPC { nrpc_index = i }) = Just i
nrpcIndex Rotate = Nothing

instance Hashable NRPC

newtype NonRedPathConds = NRPCs { nrpcs :: Seq NRPC } deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable NonRedPathConds

emptyNRPC :: NonRedPathConds
emptyNRPC = NRPCs (Seq.singleton Rotate)

addNRPC :: NameGen -> Expr -> Expr -> NonRedPathConds -> (NameGen, NonRedPathConds)
addNRPC ng e1 e2 (NRPCs nrpc) =
    -- We use the NameGen as a source of increasing numbers
    let
        (Name _ _ i _, ng') = freshSeededName (Name "NRPC" Nothing 0 Nothing) ng
        (e1', e2') = varOnRight e1 e2
    in
    (ng', NRPCs (nrpc :|> NRPC { nrpc_index = i, expr1 = e1', expr2 = e2' }))

varOnRight :: Expr -> Expr -> (Expr, Expr)
varOnRight e1@(Var _) e2 = (e2, e1)
varOnRight e1 e2 = (e1, e2)

getNRPC :: NonRedPathConds -> Maybe ((Expr, Expr), NonRedPathConds)
getNRPC (NRPCs Empty) = Nothing
getNRPC (NRPCs (Rotate :<| nrpc)) =
    case getNRPC (NRPCs (rotate nrpc)) of
        Just ((e1, e2), NRPCs others) -> Just ((e1, e2), NRPCs (others :|> Rotate))
        Nothing -> Nothing
getNRPC (NRPCs (NRPC { expr1 = e1, expr2 = e2 } :<| nrpc)) = Just ((e1, e2), NRPCs nrpc)

rotate :: Seq a -> Seq a
rotate Empty = Empty
rotate (x :<| xs) = xs :|> x

nullNRPC :: NonRedPathConds -> Bool
nullNRPC (NRPCs Empty) = False
nullNRPC _ = True

toListNRPC :: NonRedPathConds -> [(Expr, Expr)]
toListNRPC (NRPCs nrpc) = fmap (\n -> (expr1 n, expr2 n)) . Prelude.filter isNRPC $ F.toList nrpc

minIndexNRPC :: NonRedPathConds -> Int
minIndexNRPC (NRPCs Empty) = -1
minIndexNRPC (NRPCs nrpc) = minimum . mapMaybe nrpcIndex . F.toList $ nrpc

maxIndexNRPC :: NonRedPathConds -> Int
maxIndexNRPC = maximum . (-1:)  . mapMaybe nrpcIndex . F.toList . nrpcs

allIndexesNRPC :: NonRedPathConds -> HS.HashSet Int
allIndexesNRPC = HS.fromList . mapMaybe nrpcIndex . F.toList . nrpcs

toListInternalNRPC :: NonRedPathConds -> [Maybe (Int, Expr, Expr)]
toListInternalNRPC = F.toList . fmap (\case (NRPC i e1 e2) -> Just(i, e1, e2)
                                            Rotate -> Nothing) . nrpcs

pattern (:*>) :: (Expr, Expr) -> NonRedPathConds -> NonRedPathConds
pattern e1_e2 :*> nrpc <- (getNRPC -> Just (e1_e2, nrpc))

instance ASTContainer NRPC Expr where
    containedASTs (NRPC { expr1 = e1, expr2 = e2 }) = [e1, e2]
    containedASTs Rotate = []
    modifyContainedASTs f (NRPC { nrpc_index = i, expr1 = e1, expr2 = e2 }) =
        NRPC { nrpc_index = i, expr1 = f e1, expr2 = f e2 }
    modifyContainedASTs _ Rotate = Rotate

instance ASTContainer NRPC Type where
    containedASTs (NRPC { expr1 = e1, expr2 = e2 }) = containedASTs e1 <> containedASTs e2
    containedASTs Rotate = []
    modifyContainedASTs f (NRPC { nrpc_index = i, expr1 = e1, expr2 = e2 }) =
        NRPC { nrpc_index = i,expr1 = modifyContainedASTs f e1, expr2 = modifyContainedASTs f e2 }
    modifyContainedASTs _ Rotate = Rotate

instance Named NRPC where
    names (NRPC { expr1 = e1, expr2 = e2 }) = names e1 <> names e2
    names Rotate = Empty

    rename old new (NRPC { nrpc_index = i, expr1 = e1, expr2 = e2 }) =
        NRPC { nrpc_index = i, expr1 = rename old new e1, expr2 = rename old new e2 }
    rename _ _ Rotate = Rotate
    renames hm (NRPC { nrpc_index = i, expr1 = e1, expr2 = e2 }) =
        NRPC { nrpc_index = i, expr1 = renames hm e1, expr2 = renames hm e2 }
    renames _ Rotate = Rotate

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