{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.Annotations ( AnnotMap
                                       , getAnnotations
                                       , getAnnotMap -- ELIMINATE
                                       , lookupAnnot
                                       , lookupAnnotAtLoc) where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.KnownValues as KV
import G2.Internals.Language.Monad
import qualified G2.Internals.Liquid.Conversion as C
import G2.Internals.Liquid.Conversion2
import G2.Internals.Liquid.TCValues
import G2.Internals.Liquid.Types

import Language.Haskell.Liquid.Liquid()
import Language.Haskell.Liquid.Constraint.Types hiding (ghcI)
import Language.Haskell.Liquid.Types hiding (Loc, names)
import Language.Haskell.Liquid.Types.RefType

import G2.Internals.Translation.Haskell

import Control.Monad.Extra
import Data.Coerce
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
    mapM_ (annotMapToExpr2 locM) anna

annotMapToExpr2 :: M.Map Loc Name -> AnnInfo SpecType ->  LHStateM ()
annotMapToExpr2 locM (AI st) = do
    st' <- mapM (uncurry (valToExpr2 locM)) (HM.toList st)

    return undefined

valToExpr2 :: M.Map Loc Name -> SrcSpan -> [(Maybe T.Text, SpecType)] -> LHStateM ()
valToExpr2 locM srcspn =
    case mkSpan srcspn of
        Just spn -> mapM_ (valToExpr2' locM spn)
        Nothing -> return . const ()

valToExpr2' :: M.Map Loc Name -> Span -> (Maybe T.Text, SpecType) -> LHStateM ()
valToExpr2' locM spn@(Span {start = stloc}) (n, ast) = do
    e <- case M.lookup stloc locM of
            Just n -> lookupE n
            Nothing -> return Nothing

    t <- specTypeToType ast

    case (e, t) of
        (Just e', Just t') -> do
            let i = Id (Name "ret" Nothing 0 Nothing) t'
            let ai = assertionLamIds e'
            dm <- dictMapFromIds (map snd ai)

            ce <- convertSpecType dm M.empty (map snd ai) (Just i) ast
            let ce' = addIds ce ai

            insertAnnotM spn n ce'
        _ -> return ()

-- annotMapToExpr :: M.Map Loc Name -> TCValues -> State t -> ExprEnv -> AnnInfo SpecType -> AnnotMap
-- annotMapToExpr locM tcv s meenv (AI hm) =
--     AM $ HM.fromListWith (++)
--        $ mapMaybe fstSrcSpanToLoc $ HM.toList $ HM.mapWithKey (valToExpr locM tcv s meenv) hm


----- 


getAnnotMap :: TCValues -> State t -> ExprEnv -> [LHOutput] -> AnnotMap
getAnnotMap tcv s meenv ghci_cg =
    let
        locM = locLookup $ expr_env s

        anna = map lhCleanAnnotMaps ghci_cg
        annaE = map (annotMapToExpr locM tcv s meenv) anna
    in
    coerce $ mconcat $ map unAnnotMap annaE

lhCleanAnnotMaps :: LHOutput -> AnnInfo SpecType
lhCleanAnnotMaps (LHOutput {cgI = cgi, solution = sol}) =
    applySolution sol $ closeAnnots $ annotMap cgi

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

        t = C.unsafeSpecTypeToType tenv ast
        i = Id (Name "ret" Nothing 0 Nothing) t
    in
    case e of
        Just _ -> Just (n, addIds (C.convertSpecType tcv (s {expr_env = meenv}) ast i m) ai)
        Nothing -> Nothing

fstSrcSpanToLoc :: (SrcSpan, b) -> Maybe (Span, b)
fstSrcSpanToLoc (RealSrcSpan r, b) =
    Just (mkRealSpan r, b)
fstSrcSpanToLoc _ = Nothing

assertionLamIds :: Expr -> [(LamUse, Id)]
assertionLamIds = assertionLamIds' . inLams

assertionLamIds' :: Expr -> [(LamUse, Id)]
assertionLamIds' (Let _ (Assume _ (Assert _ a _))) = leadingLamUsesIds a
assertionLamIds' (Let _ (Assert _ a _)) = leadingLamUsesIds a
assertionLamIds' _ = []

addIds :: Expr -> [(LamUse, Id)] -> Expr
addIds e@(Lam _ ei _) ((u, i):is) = if i == ei then e else Lam u i $ addIds e is
addIds e _ = e

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
isLHTC _ _ = False

isLHTC2 :: Name -> Id -> Bool
isLHTC2 tcv (Id _ (TyConApp n _)) = n == tcv
isLHTC2 _ _ = False


isNumD :: KnownValues -> Id -> Bool
isNumD kv (Id _ (TyConApp n _)) = n == KV.numTC kv
isNumD _ _ = False

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
                 -- (_, x:_, _, _) -> [x]
                 -- (_, _, x:_, _) -> [x]
                 -- (_, _, _, x:_) -> [x]
                 (_, _, _, _  ) -> [ ]
  where
    rs = [x | x@(_, AnnRDf _) <- xas]
    ds = [x | x@(_, AnnDef _) <- xas]
    ls = [x | x@(_, AnnLoc _) <- xas]
    us = [x | x@(_, AnnUse _) <- xas]