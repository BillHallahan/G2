{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.FuncConstraint ( FuncConstraint (..)
                                          , SpecPart (..)
                                          -- , Polarity (..)
                                          -- , Violated (..)
                                          -- , Modification (..)
                                          -- , BoolRel (..)
                                          , FuncConstraints
                                          , emptyFC
                                          , fromSingletonFC
                                          , fromListFC
                                          , nullFC
                                          , insertFC
                                          , lookupFC
                                          , toListFC
                                          , unionFC
                                          , unionsFC
                                          , mapFC
                                          , filterFC
                                          , differenceFC
                                          , allCallNames
                                          , allCalls
                                          , allCallsFC

                                          , zeroOutUnq

                                          , printFCs
                                          , printFC) where

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax
import G2.Lib.Printers

import Data.Coerce
import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid hiding (All)

newtype FuncConstraints = FuncConstraints (M.Map Name (HS.HashSet FuncConstraint))
                     deriving (Eq, Show, Read)

data SpecPart = All | Pre | Post deriving (Eq, Show, Read, Generic)

data FuncConstraint = Call SpecPart FuncCall
                    | AndFC [FuncConstraint]
                    | OrFC [FuncConstraint]
                    | ImpliesFC FuncConstraint FuncConstraint
                    | NotFC FuncConstraint
                    deriving (Eq, Show, Read, Generic)

instance Hashable SpecPart
instance Hashable FuncConstraint

emptyFC :: FuncConstraints
emptyFC = FuncConstraints M.empty

fromSingletonFC :: FuncConstraint -> FuncConstraints
fromSingletonFC = flip insertFC emptyFC

fromListFC :: [FuncConstraint] -> FuncConstraints
fromListFC = foldr insertFC emptyFC

nullFC :: FuncConstraints -> Bool
nullFC = null . toListFC

insertFC :: FuncConstraint -> FuncConstraints -> FuncConstraints
insertFC fc (FuncConstraints fcs) =
    let
        ns = allCallNames fc
        ns' = map zeroOutUnq ns
        fc' = renames (HM.fromList $ zip ns ns') fc
        hs_fc = HS.singleton fc'
    in
    FuncConstraints $ foldr (\n -> M.insertWith HS.union n hs_fc) fcs ns'
    -- coerce (M.insertWith (++) (zeroOutUnq . funcName . constraint $ fc) [fc])

lookupFC :: Name -> FuncConstraints -> [FuncConstraint]
lookupFC n = HS.toList . M.findWithDefault HS.empty (zeroOutUnq n) . coerce

zeroOutUnq :: Name -> Name
zeroOutUnq (Name n m _ l) = Name n m 0 l

toListFC :: FuncConstraints -> [FuncConstraint]
toListFC = HS.toList . HS.unions . M.elems . coerce

unionFC :: FuncConstraints -> FuncConstraints -> FuncConstraints
unionFC (FuncConstraints fc1) (FuncConstraints fc2) =
    coerce $ M.unionWith HS.union fc1 fc2

unionsFC :: [FuncConstraints] -> FuncConstraints
unionsFC = foldr unionFC emptyFC

mapFC :: (FuncConstraint -> FuncConstraint) -> FuncConstraints -> FuncConstraints
mapFC f = coerce (M.map (HS.map f))

filterFC :: (FuncConstraint -> Bool) -> FuncConstraints -> FuncConstraints
filterFC p = coerce (M.map (HS.filter p))

differenceFC :: FuncConstraints -> FuncConstraints -> FuncConstraints
differenceFC (FuncConstraints fc1) (FuncConstraints fc2) =
    FuncConstraints $ M.differenceWith
                        (\v1 v2 ->  let
                                      d = HS.difference v1 v2
                                    in
                                    case HS.null d of
                                        True -> Nothing
                                        False -> Just d)
                      fc1 fc2

allCallNames :: FuncConstraint -> [Name]
allCallNames = map funcName . allCalls

allCalls :: FuncConstraint -> [FuncCall]
allCalls (Call _ fc) = [fc]
allCalls (AndFC fcs) = concatMap allCalls fcs
allCalls (OrFC fcs) = concatMap allCalls fcs
allCalls (ImpliesFC fc1 fc2) = allCalls fc1 ++ allCalls fc2
allCalls (NotFC fc) = allCalls fc

allCallsFC :: FuncConstraints -> [FuncCall]
allCallsFC = concatMap allCalls . toListFC

allCallsByName :: FuncConstraints -> [FuncCall]
allCallsByName = concatMap allCalls . toListFC

printFCs :: FuncConstraints -> String
printFCs fcs = intercalate "\n" (map printFC $ toListFC fcs)

printFC :: FuncConstraint -> String
printFC (Call sp (FuncCall { funcName = Name f _ _ _, arguments = ars, returns = r})) =
    let
        call_str fn = mkExprHaskell . foldl (\a a' -> App a a') (Var (Id fn TyUnknown)) $ ars
        r_str = mkExprHaskell r
    in
    case sp of
        Pre -> "(" ++ call_str (Name (f <> "_pre") Nothing 0 Nothing) ++ ")"
        Post -> "(" ++ call_str (Name (f <> "_post") Nothing 0 Nothing) ++ " " ++ r_str ++ ")"
        All -> "(" ++ call_str (Name f Nothing 0 Nothing) ++ " " ++ r_str ++ ")"
printFC (AndFC fcs) =
    case fcs of
        (f:fcs') -> foldr (\fc fcs'' -> fcs'' ++ " && " ++ printFC fc) (printFC f) fcs'
        [] -> "True"
printFC (OrFC fcs) =
    case fcs of
        (f:fcs') -> foldr (\fc fcs'' -> fcs'' ++ " || " ++ printFC fc) (printFC f) fcs'
        [] -> "False"
printFC (ImpliesFC fc1 fc2) = "(" ++ printFC fc1 ++ ") => (" ++ printFC fc2 ++ ")"
printFC (NotFC fc) = "not (" ++ printFC fc ++ ")"

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

instance Named FuncConstraints where
    names (FuncConstraints fc) = names fc
    rename old new (FuncConstraints fc) = FuncConstraints (rename old new fc)
    renames hm (FuncConstraints fc) = FuncConstraints (renames hm fc)

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
