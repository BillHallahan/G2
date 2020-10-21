{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Liquid.Inference.FuncConstraint ( FuncConstraint (..)
                                          , SpecPart (..)
                                          -- , Polarity (..)
                                          -- , Violated (..)
                                          -- , Modification (..)
                                          -- , BoolRel (..)
                                          , FuncConstraints
                                          , emptyFC
                                          , fromSingletonFC
                                          , nullFC
                                          , insertFC
                                          , lookupFC
                                          , toListFC
                                          , unionFC
                                          , unionsFC
                                          , mapFC
                                          , mapMaybeFC
                                          , filterFC
                                          , allCallNames
                                          , allCalls) where

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax
import G2.Lib.Printers

import Data.Coerce
import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M
import Data.Maybe

newtype FuncConstraints = FuncConstraints (M.Map Name [FuncConstraint])
                     deriving (Eq, Show, Read)

data SpecPart = All | Pre | Post deriving (Eq, Show, Read)

data FuncConstraint = Call SpecPart FuncCall
                    | AndFC [FuncConstraint]
                    | OrFC [FuncConstraint]
                    | ImpliesFC FuncConstraint FuncConstraint
                    | NotFC FuncConstraint
                    deriving (Eq, Show, Read)

emptyFC :: FuncConstraints
emptyFC = FuncConstraints M.empty

fromSingletonFC :: FuncConstraint -> FuncConstraints
fromSingletonFC = flip insertFC emptyFC

nullFC :: FuncConstraints -> Bool
nullFC = null . toListFC

insertFC :: FuncConstraint -> FuncConstraints -> FuncConstraints
insertFC fc (FuncConstraints fcs) =
    let
        ns = allCallNames fc
        ns' = map zeroOutUnq ns
        fc' = renames (HM.fromList $ zip ns ns') fc
    in
    FuncConstraints $ foldr (\n -> M.insertWith (++) n [fc']) fcs ns'
    -- coerce (M.insertWith (++) (zeroOutUnq . funcName . constraint $ fc) [fc])

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

mapMaybeFC :: (FuncConstraint -> Maybe FuncConstraint) -> FuncConstraints -> FuncConstraints
mapMaybeFC f = coerce (M.map (mapMaybe f))

filterFC :: (FuncConstraint -> Bool) -> FuncConstraints -> FuncConstraints
filterFC p = coerce (M.map (filter p))

allCallNames :: FuncConstraint -> [Name]
allCallNames = map funcName . allCalls

allCalls :: FuncConstraint -> [FuncCall]
allCalls (Call _ fc) = [fc]
allCalls (AndFC fcs) = concatMap allCalls fcs
allCalls (OrFC fcs) = concatMap allCalls fcs
allCalls (ImpliesFC fc1 fc2) = allCalls fc1 ++ allCalls fc2
allCalls (NotFC fc) = allCalls fc

instance ASTContainer FuncConstraint Expr where
    containedASTs (Call sp fc) = containedASTs fc
    containedASTs (AndFC fcs) = containedASTs fcs
    containedASTs (OrFC fcs) = containedASTs fcs
    containedASTs (ImpliesFC fc1 fc2) = containedASTs fc1 ++ containedASTs fc2
    containedASTs (NotFC fc) = containedASTs fc

    modifyContainedASTs f (Call sp fc) = Call sp $ modifyContainedASTs f fc
    modifyContainedASTs f (AndFC fcs) = AndFC (modifyContainedASTs f fcs)
    modifyContainedASTs f (OrFC fcs) = OrFC (modifyContainedASTs f fcs)
    modifyContainedASTs f (ImpliesFC fc1 fc2) = ImpliesFC (modifyContainedASTs f fc1) (modifyContainedASTs f fc2)
    modifyContainedASTs f (NotFC fc) = NotFC (modifyContainedASTs f fc)

instance Named FuncConstraint where
    names (Call _ fc) = names fc
    names (AndFC fcs) = names fcs
    names (OrFC fcs) = names fcs
    names (ImpliesFC fc1 fc2) = names fc1 ++ names fc2
    names (NotFC fc) = names fc

    rename old new (Call sp fc) = Call sp (rename old new fc)
    rename old new (AndFC fcs) = AndFC (rename old new fcs)
    rename old new (OrFC fcs) = OrFC (rename old new fcs)
    rename old new (ImpliesFC fc1 fc2) = ImpliesFC (rename old new fc1) (rename old new fc2)
    rename old new (NotFC fc) = NotFC (rename old new fc)

    renames hm (Call sp fc) = Call sp (renames hm fc)
    renames hm (AndFC fcs) = AndFC (renames hm fcs)
    renames hm (OrFC fcs) = OrFC (renames hm fcs)
    renames hm (ImpliesFC fc1 fc2) = ImpliesFC (renames hm fc1) (renames hm fc2)
    renames hm (NotFC fc) = NotFC (renames hm fc)
