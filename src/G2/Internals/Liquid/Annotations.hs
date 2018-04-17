{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.Annotations ( AnnotMap
                                       , getAnnotMap
                                       , lookupAnnot, amKeys) where

import G2.Internals.Language
import G2.Internals.Liquid.Conversion
import G2.Internals.Liquid.TCValues
import G2.Internals.Liquid.Types

import Language.Haskell.Liquid.Liquid()
import Language.Haskell.Liquid.Constraint.Types hiding (ghcI)
import Language.Haskell.Liquid.Types hiding (Loc)
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.UX.Annotate
import qualified Language.Haskell.Liquid.UX.Config as LHC

import Data.Coerce
import qualified Data.HashMap.Lazy as HM
import Data.List
import Data.Maybe
import qualified Data.Text as T

import FastString
import Module
import SrcLoc

newtype AnnotMap = AM (HM.HashMap Loc [Expr]) deriving (Eq, Show)

amKeys (AM am) = HM.keys am

lookupAnnot :: Name -> AnnotMap -> Maybe [Expr]
lookupAnnot (Name n (Just m) _ (Just l)) =
    HM.lookup l . coerce
lookupAnnot (Name n Nothing _ (Just l)) =
    HM.lookup l . coerce
lookupAnnot _ = const Nothing

getAnnotMap :: LHC.Config -> TCValues -> State t -> [LHOutput] -> AnnotMap
getAnnotMap lh_config tcv s ghci_cg =
    let
        anna = map lhCleanAnnotMaps ghci_cg
    in
    annotMapToExpr tcv s $ mconcat anna

lhCleanAnnotMaps :: LHOutput -> AnnInfo SpecType
lhCleanAnnotMaps (LHOutput {ghcI = ghci, cgI = cgi, solution = sol}) =
    applySolution sol $ coerce $ HM.map (mapMaybe annotExprSpecType) $ coerce $ annotMap cgi

-- From https://github.com/ucsd-progsys/liquidhaskell/blob/75184064eed475289648ead76e3e9d370b168e66/src/Language/Haskell/Liquid/Types.hs
-- newtype AnnInfo a = AI (M.HashMap SrcSpan [(Maybe Text, a)])

annotMapToExpr :: TCValues -> State t -> AnnInfo SpecType -> AnnotMap
annotMapToExpr tcv s (AI hm) =
    AM $ HM.fromListWith (++)
       $ mapMaybe fstSrcSpanToLoc $ HM.toList $ HM.map (valToExpr tcv s) hm

valToExpr :: TCValues -> State t -> [(Maybe T.Text, SpecType)] -> [Expr]
valToExpr tcv s = map (valToExpr' tcv s)

valToExpr' :: TCValues -> State t -> (Maybe T.Text, SpecType) -> Expr
valToExpr' tcv s (_, ast) = convertSpecType tcv s ast (Id (Name "ret" Nothing 0 Nothing) TyBottom) Nothing

annotExprSpecType :: (Maybe T.Text, Annot SpecType) -> Maybe (Maybe T.Text, SpecType)
annotExprSpecType (a, AnnUse st) = Just (a, st)
annotExprSpecType (a, AnnDef st) = Just (a, st)
annotExprSpecType (a, AnnRDf st) = Just (a, st)
annotExprSpecType (a, AnnLoc _) = Nothing

fstSrcSpanToLoc :: (SrcSpan, b) -> Maybe (Loc, b)
fstSrcSpanToLoc (RealSrcSpan r, b) =
    let
        l = realSrcSpanStart r
    in
    Just (Loc {line = srcLocLine l, col = srcLocCol l, file = unpackFS $ srcLocFile l}, b)
fstSrcSpanToLoc _ = Nothing

rightFstToLeft :: (a, [(b, c)]) -> [((a, b), [c])]
rightFstToLeft (a, xs) =
    map (\(b, c) -> ((a, b), [c])) xs

instance ASTContainer AnnotMap Expr where
    containedASTs =  concat . HM.elems . coerce
    modifyContainedASTs f = AM . HM.map (modifyContainedASTs f) . coerce

