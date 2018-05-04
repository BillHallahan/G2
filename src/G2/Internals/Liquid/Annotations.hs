{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.Annotations ( AnnotMap
                                       , getAnnotMap
                                       , lookupAnnot
                                       , lookupAnnotAtLoc) where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.KnownValues as KV
import G2.Internals.Liquid.Conversion
import G2.Internals.Liquid.TCValues
import G2.Internals.Liquid.Types

import Language.Haskell.Liquid.Liquid()
import Language.Haskell.Liquid.Constraint.Types hiding (ghcI)
import Language.Haskell.Liquid.Types hiding (Loc, names)
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.UX.Annotate
import qualified Language.Haskell.Liquid.UX.Config as LHC

import G2.Internals.Translation.Haskell

import Data.Coerce
import qualified Data.HashMap.Lazy as HM
import Data.Hashable
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import FastString
import Module
import SrcLoc

import Debug.Trace

newtype AnnotMap = AM { unAnnotMap :: HM.HashMap Span [(Maybe T.Text, Expr)] } deriving (Eq, Show)

lookupAnnot :: Name -> AnnotMap -> Maybe [(Maybe T.Text, Expr)]
lookupAnnot (Name n _ _ (Just s)) =
    HM.lookup s . unAnnotMap
lookupAnnot _ = const Nothing

lookupAnnotAtLoc :: Name -> AnnotMap -> Maybe [(Maybe T.Text, Expr)]
lookupAnnotAtLoc (Name n _ _ (Just (Span {start = l}))) =
    Just . concatMap snd . find (\(Span {start = l'}, _) -> l == l') . HM.toList . unAnnotMap
lookupAnnotAtLoc _ = const Nothing

getAnnotMap :: LHC.Config -> TCValues -> State t -> ExprEnv -> [LHOutput] -> AnnotMap
getAnnotMap lh_config tcv s@(State {expr_env = eenv}) meenv ghci_cg =
    let
        locM = locLookup $ expr_env s

        anna = map lhCleanAnnotMaps ghci_cg
        annaE = map (annotMapToExpr locM tcv s meenv) anna
    in
    coerce $ mconcat $ map unAnnotMap annaE

lhCleanAnnotMaps :: LHOutput -> AnnInfo SpecType
lhCleanAnnotMaps (LHOutput {ghcI = ghci, cgI = cgi, solution = sol}) =
    applySolution sol $ {- coerce $ HM.map (mapMaybe annotExprSpecType) $ -} closeAnnots $ annotMap cgi

unAnnInfo :: AnnInfo SpecType -> HM.HashMap SrcSpan [(Maybe T.Text, SpecType)]
unAnnInfo (AI hm) = hm

-- From https://github.com/ucsd-progsys/liquidhaskell/blob/75184064eed475289648ead76e3e9d370b168e66/src/Language/Haskell/Liquid/Types.hs
-- newtype AnnInfo a = AI (M.HashMap SrcSpan [(Maybe Text, a)])

annotMapToExpr :: M.Map Loc Name -> TCValues -> State t -> ExprEnv -> AnnInfo SpecType -> AnnotMap
annotMapToExpr locM tcv s meenv (AI hm) =
    AM $ HM.fromListWith (++)
       $ mapMaybe fstSrcSpanToLoc $ HM.toList $ HM.mapWithKey (valToExpr locM tcv s meenv) hm

valToExpr :: M.Map Loc Name -> TCValues -> State t -> ExprEnv -> SrcSpan -> [(Maybe T.Text, SpecType)] -> [(Maybe T.Text, Expr)]
valToExpr locM tcv s meenv srcspn =
    case mkSpan srcspn of
        Just spn -> mapMaybe (valToExpr' locM tcv s meenv spn)
        Nothing -> const []

valToExpr' :: M.Map Loc Name -> TCValues -> State t -> ExprEnv -> Span -> (Maybe T.Text, SpecType) -> Maybe (Maybe T.Text, Expr)
valToExpr' locM tcv s@(State {expr_env = eenv, type_env = tenv, known_values = kv}) meenv (Span {start = stloc}) (n, ast) =
    let
        e = flip E.lookup (E.filter hasAssumeAssert eenv) =<<  M.lookup stloc locM
        ai = maybe [] assertionLamIds e
        m = fmap (lamIdMap kv tcv . leadingLamIds) e

        t = unsafeSpecTypeToType tenv ast
        i = Id (Name "ret" Nothing 0 Nothing) t
    in
    case e of
        Just e -> Just (n, addIds (convertSpecType tcv (s {expr_env = meenv}) ast i m) ai)
        Nothing -> Nothing

fstSrcSpanToLoc :: (SrcSpan, b) -> Maybe (Span, b)
fstSrcSpanToLoc (RealSrcSpan r, b) =
    Just (mkRealSpan r, b)
fstSrcSpanToLoc _ = Nothing

rightFstToLeft :: (a, [(b, c)]) -> [((a, b), [c])]
rightFstToLeft (a, xs) =
    map (\(b, c) -> ((a, b), [c])) xs

assertionLamIds :: Expr -> [Id]
assertionLamIds = assertionLamIds' . inLams

assertionLamIds' :: Expr -> [Id]
assertionLamIds' (Let _ (Assume _ (Assert _ a _))) = leadingLamIds a
assertionLamIds' (Let _ (Assert _ a _)) = leadingLamIds a
assertionLamIds' e = []

addIds :: Expr -> [Id] -> Expr
addIds e [] = e
addIds e@(Lam ei _) (i:is) = if i == ei then e else Lam i $ addIds e is

hasAssumeAssert :: Expr -> Bool
hasAssumeAssert = hasAssumeAssert' . inLams

hasAssumeAssert' :: Expr -> Bool
hasAssumeAssert' (Let _ (Assume _ _)) = True
hasAssumeAssert' (Let _ (Assert _ _ _)) = True
hasAssumeAssert' _ = False

lamIdMap :: KnownValues -> TCValues -> [Id] -> M.Map Name Type
lamIdMap kv tcv =
    M.fromList . map (\(Id n t) -> (n, t)) . filter (\i -> isLHTC tcv i || isNumD kv i)

isLHTC :: TCValues -> Id -> Bool
isLHTC tcv (Id _ (TyConApp n _)) = n == lhTC tcv
isLHTC _ i = False

isNumD :: KnownValues -> Id -> Bool
isNumD kv (Id _ (TyConApp n _)) = n == KV.numTC kv
isNumD _ i = False

instance ASTContainer AnnotMap Expr where
    containedASTs =  map snd . concat . HM.elems . unAnnotMap
    modifyContainedASTs f = AM . HM.map (modifyContainedASTs f) . coerce

instance Named AnnotMap where
    names = names . unAnnotMap
    rename old new = coerce . rename old new . unAnnotMap
    renames hm = coerce . renames hm . unAnnotMap

closeAnnots :: AnnInfo (Annot SpecType) -> AnnInfo SpecType
closeAnnots = closeA . filterA . collapseA

closeA :: AnnInfo (Annot b) -> AnnInfo b
closeA a@(AI m)   = cf <$> a
  where
    cf (AnnLoc l)  = case m `mlookup` l of
                      [(_, AnnUse t)] -> t
                      [(_, AnnDef t)] -> t
                      [(_, AnnRDf t)] -> t
                      _               -> error $ "malformed AnnInfo: " ++ show l
    cf (AnnUse t) = t
    cf (AnnDef t) = t
    cf (AnnRDf t) = t

mlookup    :: (Eq k, Show k, Hashable k) => HM.HashMap k v -> k -> v
mlookup m k = fromMaybe err $ HM.lookup k m
  where
    err     = error $ "mlookup: unknown key " ++ show k

filterA :: AnnInfo (Annot t) -> AnnInfo (Annot t)
filterA (AI m) = AI (HM.filter ff m)
  where
    ff [(_, AnnLoc l)] = l `HM.member` m
    ff _               = True

collapseA :: AnnInfo (Annot t) -> AnnInfo (Annot t)
collapseA (AI m) = AI (fmap pickOneA m)

pickOneA :: [(t, Annot t1)] -> [(t, Annot t1)]
pickOneA xas = case (rs, ds, ls, us) of
                 (x:_, _, _, _) -> [x]
                 (_, x:_, _, _) -> [x]
                 (_, _, x:_, _) -> [x]
                 (_, _, _, x:_) -> [x]
                 (_, _, _, _  ) -> [ ]
  where
    rs = [x | x@(_, AnnRDf _) <- xas]
    ds = [x | x@(_, AnnDef _) <- xas]
    ls = [x | x@(_, AnnLoc _) <- xas]
    us = [x | x@(_, AnnUse _) <- xas]