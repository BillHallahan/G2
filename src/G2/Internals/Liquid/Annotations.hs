{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.Annotations ( AnnotMap
                                       , getAnnotations
                                       , lookupAnnot
                                       , lookupAnnotAtLoc) where

import G2.Internals.Language
import G2.Internals.Language.Monad
import G2.Internals.Liquid.Conversion
import G2.Internals.Liquid.Types

import Language.Haskell.Liquid.Liquid()
import Language.Haskell.Liquid.Constraint.Types hiding (ghcI)
import Language.Haskell.Liquid.Types hiding (Loc, names)
import Language.Haskell.Liquid.Types.RefType

import G2.Internals.Translation.Haskell

import qualified Data.HashMap.Lazy as HM
import Data.Hashable
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import SrcLoc

import Debug.Trace

lookupAnnot :: Name -> AnnotMap -> Maybe [(Maybe T.Text, Expr)]
lookupAnnot (Name _ _ _ (Just s)) =
    HM.lookup s . unAnnotMap
lookupAnnot _ = const Nothing

lookupAnnotAtLoc :: Name -> AnnotMap -> Maybe [(Maybe T.Text, Expr)]
lookupAnnotAtLoc (Name _ _ _ (Just (Span {start = l}))) =
    Just . concatMap snd . find (\(Span {start = l'}, _) -> l == l') . HM.toList . unAnnotMap
lookupAnnotAtLoc _ = const Nothing

getAnnotations :: [LHOutput] -> LHStateM ()
getAnnotations ghci_cg = do
    locM <- return . locLookup =<< exprEnv

    let anna = map lhCleanAnnotMaps ghci_cg
    mapM_ (annotMapToExpr locM) anna

annotMapToExpr :: M.Map Loc Name -> AnnInfo SpecType ->  LHStateM ()
annotMapToExpr locM (AI st) = mapM_ (uncurry (valToExpr locM)) (HM.toList st)

valToExpr :: M.Map Loc Name -> SrcSpan -> [(Maybe T.Text, SpecType)] -> LHStateM ()
valToExpr locM srcspn =
    case mkSpan srcspn of
        Just spn -> mapM_ (valToExpr' locM spn)
        Nothing -> return . const ()

valToExpr' :: M.Map Loc Name -> Span -> (Maybe T.Text, SpecType) -> LHStateM ()
valToExpr' locM spn@(Span {start = stloc}) (n, ast) = do
    e <- case M.lookup stloc locM of
            Just n' -> lookupE n'
            Nothing -> return Nothing

    t <- specTypeToType ast

    case (e, t) of
        (Just e', Just t') -> do
            let i = Id (Name "ret" Nothing 0 Nothing) t'
            let ai = leadingLamUsesIds e' -- assertionLamIds e'
            dm <- dictMapFromIds (map snd ai)

            ce <- convertSpecType dm M.empty (map snd ai) (Just i) ast
            let ce' = addIds ce (ai ++ [(TermL, i)])

            insertAnnotM spn n ce'
        _ -> return ()

lhCleanAnnotMaps :: LHOutput -> AnnInfo SpecType
lhCleanAnnotMaps (LHOutput {cgI = cgi, solution = sol}) =
    applySolution sol $ closeAnnots $ annotMap cgi

assertionLamIds :: Expr -> [(LamUse, Id)]
assertionLamIds = assertionLamIds' . inLams

assertionLamIds' :: Expr -> [(LamUse, Id)]
assertionLamIds' (Let _ (Assume _ (Assert _ a _))) = leadingLamUsesIds a
assertionLamIds' (Let _ (Assert _ a _)) = leadingLamUsesIds a
assertionLamIds' _ = []

addIds :: Expr -> [(LamUse, Id)] -> Expr
addIds e ((u, i):is) = Lam u i $ addIds e is
-- addIds e@(Lam _ ei _) ((u, i):is) = if i == ei then e else Lam u i $ addIds e is
addIds e _ = e

-- modeled after Language.Haskell.Liquid.UX.Annotate
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
                 (_, _, x:_, _) -> trace ("Loc") []
                 (_, _, _, x:_) -> [x]

                 -- (_, x:_, _, _) -> [x]
                 -- (_, _, x:_, _) -> [x]
                 -- (_, _, _, x:_) -> [x]
                 (_, _, _, _  ) -> [ ]
  where
    rs = [x | x@(_, AnnRDf _) <- xas]
    ds = [x | x@(_, AnnDef _) <- xas]
    ls = [x | x@(_, AnnLoc _) <- xas]
    us = [x | x@(_, AnnUse _) <- xas]
