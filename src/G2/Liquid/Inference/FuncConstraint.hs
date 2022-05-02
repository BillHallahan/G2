{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.FuncConstraint ( FuncConstraint (..)
                                          , SpecPart (..)
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
                                          , allConcCalls
                                          , allCallsFC
                                          , allConcCallsFC

                                          , zeroOutUnq

                                          , printFCs
                                          , printConcFCs
                                          , printAbsFCs

                                          , printFC
                                          , printConcFC
                                          , printAbsFC) where

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Support
import G2.Language.Syntax
import G2.Lib.Printers
import G2.Liquid.Interface
import G2.Liquid.Types

import Data.Coerce
import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M
import Data.Monoid hiding (All)

newtype FuncConstraints = FuncConstraints (M.Map Name (HS.HashSet FuncConstraint))
                     deriving (Eq, Show, Read)

data SpecPart = All | Pre | Post deriving (Eq, Show, Read, Generic)

data FuncConstraint = Call SpecPart ConcAbsFuncCall
                    | AndFC [FuncConstraint]
                    | OrFC [FuncConstraint]
                    | ImpliesFC FuncConstraint FuncConstraint
                    | NotFC FuncConstraint
                    deriving (Eq, Show, Read, Generic)

instance Hashable SpecPart
instance Hashable FuncConstraint

-- | An empty `FuncConstraints`.
emptyFC :: FuncConstraints
emptyFC = FuncConstraints M.empty

-- | A `FuncConstraint`s containing a single `FuncConstraint`.
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

-- | Filter all `FuncConstraint`s that satisfy the given predicate.
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

-- | Find the names of all function calls in the given `FuncConstraint`.
allCallNames :: FuncConstraint -> [Name]
allCallNames = map (caFuncName) . allCalls

-- | Find all `ConcAbsFuncCall`s in the given `FuncConstraint`.
allCalls :: FuncConstraint -> [ConcAbsFuncCall]
allCalls (Call _ fc) = [fc]
allCalls (AndFC fcs) = concatMap allCalls fcs
allCalls (OrFC fcs) = concatMap allCalls fcs
allCalls (ImpliesFC fc1 fc2) = allCalls fc1 ++ allCalls fc2
allCalls (NotFC fc) = allCalls fc

allConcCalls :: FuncConstraint -> [FuncCall]
allConcCalls = map conc_fcall . allCalls

allCallsFC :: FuncConstraints -> [ConcAbsFuncCall]
allCallsFC = concatMap allCalls . toListFC

allConcCallsFC :: FuncConstraints -> [FuncCall]
allConcCallsFC = map conc_fcall . allCallsFC

allCallsByName :: FuncConstraints -> [ConcAbsFuncCall]
allCallsByName = concatMap allCalls . toListFC

printFCs :: (ConcAbsFuncCall -> FuncCall) -> FuncConstraints -> String
printFCs f fcs =
    intercalate "\n" . map (printFC f) $ toListFC fcs

printConcFCs :: FuncConstraints -> String
printConcFCs = printFCs conc_fcall

printAbsFCs :: FuncConstraints -> String
printAbsFCs = printFCs (fcall . abs_fcall)

printFC :: (ConcAbsFuncCall -> FuncCall) -> FuncConstraint -> String
printFC f (Call sp ca_fc) =
    let
        cfc = f ca_fc
    in
    case sp of
        Pre -> "(" ++ printPreCall cfc ++ ")"
        Post -> "(" ++ printPostCall cfc ++ ")"
        All -> "(" ++ printAllCall cfc ++ ")"
printFC f (AndFC fcs) =
    case fcs of
        (fc:fcs') -> foldr (\fc' fcs'' -> fcs'' ++ " && " ++ printFC f fc') (printFC f fc) fcs'
        [] -> "True"
printFC f (OrFC fcs) =
    case fcs of
        (fc:fcs') -> foldr (\fc' fcs'' -> fcs'' ++ " || " ++ printFC f fc') (printFC f fc) fcs'
        [] -> "False"
printFC f (ImpliesFC fc1 fc2) = "(" ++ printFC f fc1 ++ ") => (" ++ printFC f fc2 ++ ")"
printFC f (NotFC fc) = "not (" ++ printFC f fc ++ ")"

printConcFC :: FuncConstraint -> String
printConcFC = printFC conc_fcall

printAbsFC :: FuncConstraint -> String
printAbsFC = printFC (fcall . abs_fcall)

printPreCall :: FuncCall -> String
printPreCall (FuncCall { funcName = Name f _ _ _, arguments = ars, returns = r}) =
    printHaskellDirty . foldl (\a a' -> App a a') (Var (Id (Name (f <> "_pre") Nothing 0 Nothing) TyUnknown)) $ ars

printPostCall :: FuncCall -> String
printPostCall (FuncCall { funcName = Name f _ _ _, arguments = ars, returns = r}) =
    let
        cll = printHaskellDirty . foldl (\a a' -> App a a') (Var (Id (Name (f <> "_post") Nothing 0 Nothing) TyUnknown)) $ ars
        r_str = printHaskellDirty r
    in
    cll ++ " " ++ r_str ++ ")"

printAllCall :: FuncCall -> String
printAllCall (FuncCall { funcName = f, arguments = ars, returns = r}) =
    let
        cll = printHaskellDirty . foldl (\a a' -> App a a') (Var (Id f TyUnknown)) $ ars
        r_str = printHaskellDirty r
    in
    cll ++ " " ++ r_str ++ ")"

instance ASTContainer FuncConstraint Expr where
    containedASTs (Call _ fc) = containedASTs fc
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
    names (ImpliesFC fc1 fc2) = names fc1 <> names fc2
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
