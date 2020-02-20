{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Liquid.Inference.FuncConstraint ( FuncConstraint (..)
                                          , FuncConstraints
                                          , emptyFC
                                          , insertPostFC
                                          , lookupPostFC
                                          , allFC
                                          , unionFC
                                          , unionsFC
                                          , filterFC ) where

import G2.Language.AST
import G2.Language.Syntax

import qualified Data.Map as M

data FuncConstraints =
    FuncConstraints { pre :: M.Map Name [FuncConstraint] -- ^ Use to refine the precondition
                    , post :: M.Map Name [FuncConstraint] -- ^ Use to refine the postcondition 
                    } deriving (Eq, Show, Read)

data FuncConstraint = Pos { constraint :: FuncCall }
                    | Neg { constraint :: FuncCall }
                    deriving (Eq, Show, Read)

emptyFC :: FuncConstraints
emptyFC = FuncConstraints M.empty M.empty

insertPostFC :: FuncConstraint -> FuncConstraints -> FuncConstraints
insertPostFC fc fcs@(FuncConstraints { post = p }) =
    fcs { post = M.insertWith (++) (zeroOutUnq . funcName . constraint $ fc) [fc] p }

lookupPostFC :: Name -> FuncConstraints -> [FuncConstraint]
lookupPostFC n = M.findWithDefault [] (zeroOutUnq n) . post

zeroOutUnq :: Name -> Name
zeroOutUnq (Name n m _ l) = Name n m 0 l

allFC :: FuncConstraints -> [FuncConstraint]
allFC fc = concat $ M.elems (pre fc) ++ M.elems (post fc)

unionFC :: FuncConstraints -> FuncConstraints -> FuncConstraints
unionFC fc1 fc2 =
    FuncConstraints { pre = pre fc1 `M.union` pre fc2
                    , post = post fc1 `M.union` post fc2 }

unionsFC :: [FuncConstraints] -> FuncConstraints
unionsFC = foldr unionFC emptyFC

filterFC :: (FuncConstraint -> Bool) -> FuncConstraints -> FuncConstraints
filterFC p fc =
    FuncConstraints { pre = M.map (filter p) (pre fc)
                    , post = M.map (filter p) (post fc) }

instance ASTContainer FuncConstraint Expr where
    containedASTs = containedASTs . constraint

    modifyContainedASTs f (Pos c) = Pos $ modifyContainedASTs f c
    modifyContainedASTs f (Neg c) = Neg $ modifyContainedASTs f c