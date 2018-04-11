{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.Annotations ( AnnotMap
                                       , getAnnotMap
                                       , lookupAnnot, amKeys) where

import G2.Internals.Language
import G2.Internals.Liquid.Conversion
import G2.Internals.Liquid.TCValues

import Language.Haskell.Liquid.Constraint.Types
import Language.Haskell.Liquid.Types hiding (Loc)

import qualified Data.HashMap.Lazy as HM
import Data.Maybe
import qualified Data.Text as T

import SrcLoc

newtype AnnotMap = AM (HM.HashMap (Loc, Maybe T.Text) (Maybe Expr)) deriving (Eq, Show)

amKeys (AM am) = HM.keys am

lookupAnnot :: Name -> AnnotMap -> Maybe Expr
lookupAnnot (Name n (Just m) _ (Just l)) (AM am) =
    case HM.lookup (l, Just $ m `T.append` "." `T.append` n) am of
        Just e -> e
        Nothing -> Nothing
lookupAnnot (Name n Nothing _ (Just l)) (AM am) =
    case HM.lookup (l, Just n) am of
        Just e -> e
        Nothing -> Nothing
lookupAnnot _ _ = Nothing

getAnnotMap :: TCValues -> State t -> [CGInfo] -> AnnotMap
getAnnotMap tcv s cgi =
    let
        am = mconcat $ map annotMap cgi
        am' = annotMapToExpr tcv s am
    in
    am'

-- From https://github.com/ucsd-progsys/liquidhaskell/blob/75184064eed475289648ead76e3e9d370b168e66/src/Language/Haskell/Liquid/Types.hs
-- newtype AnnInfo a = AI (M.HashMap SrcSpan [(Maybe Text, a)])

annotMapToExpr :: TCValues -> State t -> AnnInfo (Annot SpecType) -> AnnotMap
annotMapToExpr tcv s (AI hm) =
    AM $ HM.fromList $ concatMap rightFstToLeft
       $ mapMaybe fstSrcSpanToLoc $ HM.toList $ HM.map (annotValToExpr tcv s) hm

annotValToExpr :: TCValues -> State t -> [(Maybe T.Text, Annot SpecType)] -> [(Maybe T.Text, Maybe Expr)]
annotValToExpr tcv s = map (annotValToExpr' tcv s)

annotValToExpr' :: TCValues -> State t -> (Maybe T.Text, Annot SpecType) -> (Maybe T.Text, Maybe Expr)
annotValToExpr' tcv s (t, ast) = (t, annotExpr tcv s ast)

annotExpr :: TCValues -> State t -> Annot SpecType -> Maybe Expr
annotExpr tcv s (AnnUse st) = Just $ convertSpecType tcv s st (Id (Name "ret" Nothing 0 Nothing) TyBottom) Nothing
annotExpr tcv s (AnnDef st) = Just $ convertSpecType tcv s st (Id (Name "ret" Nothing 0 Nothing) TyBottom) Nothing
annotExpr tcv s (AnnRDf st) = Just $ convertSpecType tcv s st (Id (Name "ret" Nothing 0 Nothing) TyBottom) Nothing
annotExpr _ _ (AnnLoc _) = Nothing

fstSrcSpanToLoc :: (SrcSpan, b) -> Maybe (Loc, b)
fstSrcSpanToLoc (RealSrcSpan r, b) =
    let
        l = realSrcSpanStart r
    in
    Just (Loc {line = srcLocLine l, col = srcLocCol l}, b)
fstSrcSpanToLoc _ = Nothing

rightFstToLeft :: (a, [(b, c)]) -> [((a, b), c)]
rightFstToLeft (a, xs) =
    map (\(b, c) -> ((a, b), c)) xs
