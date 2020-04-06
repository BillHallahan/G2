{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Liquid.Inference.FuncConstraint ( FuncConstraint (..)
                                          , Polarity (..)
                                          , Violated (..)
                                          , Modification (..)
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
                                          , mapMaybeFC
                                          , filterFC

                                          , constraining

                                          , printFC
                                          , printFCs ) where

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax
import G2.Lib.Printers

import Data.Coerce
import Data.List
import qualified Data.Map as M
import Data.Maybe

newtype FuncConstraints = FuncConstraints (M.Map Name [FuncConstraint])
                     deriving (Eq, Show, Read)

data Polarity = Pos | Neg deriving (Eq, Show, Read)

data Violated = Pre | Post deriving (Eq, Show, Read)

data Modification =
      SwitchImplies [Name] -- ^ Change the boolean relation to Implies if the
                           -- spec of any function in the list changes
    | Delete [Name] -- ^ Delete the constraint if the spec of any function in
                    -- the list changes
    | None -- ^ The constraint should not be modified
    deriving (Eq, Show, Read)

data BoolRel = BRImplies | BRAnd deriving (Eq, Show, Read)

data FuncConstraint =
    FC { polarity :: Polarity
       , violated :: Violated
       , modification :: Modification
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

mapMaybeFC :: (FuncConstraint -> Maybe FuncConstraint) -> FuncConstraints -> FuncConstraints
mapMaybeFC f = coerce (M.map (mapMaybe f))

filterFC :: (FuncConstraint -> Bool) -> FuncConstraints -> FuncConstraints
filterFC p = coerce (M.map (filter p))

constraining :: FuncConstraint -> Name
constraining = funcName . constraint

printFCs :: FuncConstraints -> String
printFCs = intercalate "\n" . map printFC . toListFC

printFC :: FuncConstraint -> String
printFC fc@(FC { constraint = c}) =
    let
      f = funcName c
      cl = mkExprHaskell . foldl (\a a' -> App a a') (Var (Id f TyUnknown)) $ arguments c

      r = mkExprHaskell $ returns c
      r' = case polarity fc of
              Pos -> r
              Neg -> "NOT " ++ r

      md = case modification fc of
                    SwitchImplies ns -> "switch on " ++ show (map nameOcc ns)
                    Delete ns -> "delete on " ++ show (map nameOcc ns)
                    None -> ""
    in
    case bool_rel fc of
        BRAnd -> cl ++ " AND " ++ r' ++ " " ++ md
        BRImplies -> cl ++ " => " ++ r' ++ " " ++ md
instance ASTContainer FuncConstraint Expr where
    containedASTs = containedASTs . constraint

    modifyContainedASTs f (FC p v g gp c) = FC p v g gp $ modifyContainedASTs f c
