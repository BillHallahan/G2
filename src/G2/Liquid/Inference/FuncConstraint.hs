{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Liquid.Inference.FuncConstraint ( FuncConstraint (..)
                                          , Polarity (..)
                                          , Violated (..)
                                          , BoolRel (..)
                                          , FuncConstraints
                                          , emptyFC
                                          , nullFC
                                          , insertFC
                                          , lookupFC
                                          , toListFC
                                          , unionFC
                                          , unionsFC
                                          , mapFC
                                          , filterFC

                                          , constraining ) where

import G2.Language.AST
import G2.Language.Syntax

import Data.Coerce
import qualified Data.Map as M

newtype FuncConstraints = FuncConstraints (M.Map Name [FuncConstraint])
                     deriving (Eq, Show, Read)

data Polarity = Pos | Neg deriving (Eq, Show, Read)

data Violated = Pre | Post deriving (Eq, Show, Read)

data BoolRel = BRImplies | BRAnd deriving (Eq, Show, Read)

data FuncConstraint =
    FC { polarity :: Polarity
       , violated :: Violated
       , generated_by :: [Name] -- ^ Which function generated the given constraint?
       , bool_rel :: BoolRel -- ^ True iff generated_by's spec has not changed since the FC was created
       , constraint :: FuncCall }
       deriving (Eq, Show, Read)

emptyFC :: FuncConstraints
emptyFC = FuncConstraints M.empty

nullFC :: FuncConstraints -> Bool
nullFC = null . toListFC

insertFC :: FuncConstraint -> FuncConstraints -> FuncConstraints
insertFC fc  =
    coerce (M.insertWith (++) (zeroOutUnq . funcName . constraint $ fc) [fc])

lookupFC :: Name -> FuncConstraints -> [FuncConstraint]
lookupFC n = M.findWithDefault [] (zeroOutUnq n) . coerce

zeroOutUnq :: Name -> Name
zeroOutUnq (Name n m _ l) = Name n m 0 l

toListFC :: FuncConstraints -> [FuncConstraint]
toListFC = concat . M.elems . coerce

unionFC :: FuncConstraints -> FuncConstraints -> FuncConstraints
unionFC (FuncConstraints fc1) (FuncConstraints fc2) =
    coerce $ M.unionWith (++) fc1 fc2

unionsFC :: [FuncConstraints] -> FuncConstraints
unionsFC = foldr unionFC emptyFC

mapFC :: (FuncConstraint -> FuncConstraint) -> FuncConstraints -> FuncConstraints
mapFC f = coerce (M.map (map f))

filterFC :: (FuncConstraint -> Bool) -> FuncConstraints -> FuncConstraints
filterFC p = coerce (M.map (filter p))

constraining :: FuncConstraint -> Name
constraining = funcName . constraint

instance ASTContainer FuncConstraint Expr where
    containedASTs = containedASTs . constraint

    modifyContainedASTs f (FC p v g gp c) = FC p v g gp $ modifyContainedASTs f c
