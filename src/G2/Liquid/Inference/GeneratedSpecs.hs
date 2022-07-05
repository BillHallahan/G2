{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.GeneratedSpecs ( GeneratedSpecs
                                          , emptyGS
                                          , namesGS

                                          , nullAssumeGS

                                          , unionDroppingGS
                                          
                                          , insertAssumeGS
                                          , insertAssertGS
                                          , insertNewSpec
                                          , insertQualifier
                                          , switchAssumesToAsserts

                                          , lookupAssertGS

                                          , filterAssertsKey
                                          , filterOutSpecs
                                          , filterOutAssertSpecs

                                          , addSpecsToGhcInfos
                                          , addAssumedSpecsToGhcInfos
                                          , addQualifiersToGhcInfos
                                          
                                          , deleteAssume
                                          , deleteAssert
                                          , deleteAllAssumes
                                          , deleteAllAsserts

                                          , allExprs

                                          , genSpec
                                          , insertMissingAssertSpec ) where

import qualified G2.Language as G2
import G2.Liquid.Helpers
import G2.Liquid.Types
import G2.Liquid.Inference.PolyRef

import Language.Haskell.Liquid.Constraint.Init
import Language.Haskell.Liquid.Types hiding
          (TargetInfo (..), TargetSrc (..), TargetSpec (..), GhcSpec (..), qualifiers)
import Language.Haskell.Liquid.Types.Fresh
import Language.Fixpoint.Types.Refinements
import Language.Haskell.Liquid.Types.RefType
import Language.Fixpoint.Types

import qualified Control.Monad.State as S
import Data.Coerce
import Data.List
import qualified Data.Text as T
import qualified Data.Map as M

import Name (nameOccName, occNameString)
import Var

import Debug.Trace

data GeneratedSpecs = GeneratedSpecs { assert_specs :: M.Map G2.Name [PolyBound Expr]
                                     , assume_specs :: M.Map G2.Name [PolyBound Expr]
                                     , qualifiers :: [Qualifier] } deriving (Eq, Show)

emptyGS :: GeneratedSpecs
emptyGS = GeneratedSpecs M.empty M.empty []

nullAssumeGS :: GeneratedSpecs -> Bool
nullAssumeGS = M.null . assume_specs

namesGS :: GeneratedSpecs -> [G2.Name]
namesGS = M.keys . assert_specs

insertAssumeGS :: G2.Name -> [PolyBound Expr] -> GeneratedSpecs -> GeneratedSpecs
insertAssumeGS n e gs =
    gs { assume_specs = M.insert (zeroOutUnq n) e (assume_specs gs) }

insertAssertGS :: G2.Name -> [PolyBound Expr] -> GeneratedSpecs -> GeneratedSpecs
insertAssertGS n e gs =
    gs { assert_specs = M.insert (zeroOutUnq n) e (assert_specs gs) }

insertQualifier :: Qualifier -> GeneratedSpecs -> GeneratedSpecs
insertQualifier qual gs@(GeneratedSpecs { qualifiers = quals }) =
    gs { qualifiers = qual:quals }

insertNewSpec :: G2.Name -> [PolyBound Expr] -> GeneratedSpecs -> GeneratedSpecs
insertNewSpec n new_spec =
    insertAssertGS n (pre new_spec) . insertAssumeGS n (post new_spec)
    where
        pre xs = init xs ++ [PolyBound PTrue []]
        post xs = replicate (length $ init xs) (PolyBound PTrue []) ++ [last xs]

switchAssumesToAsserts :: GeneratedSpecs -> GeneratedSpecs
switchAssumesToAsserts gs =
    gs { assert_specs =
            M.unionWith
                (zipWith
                    (zipWithMaybePB (\s1 s2 -> PAnd [maybe PTrue id s1, maybe PTrue id s2]))
                )
                (assert_specs gs) (assume_specs gs)
       , assume_specs = M.empty }

-- | Merges two GeneratedSpecs, favoring constraints in the first generated specs
unionDroppingGS :: GeneratedSpecs -> GeneratedSpecs -> GeneratedSpecs
unionDroppingGS gs1 gs2 =
    GeneratedSpecs { assert_specs = M.union (assert_specs gs1) (assert_specs gs2)
                   , assume_specs = M.union (assume_specs gs1) (assume_specs gs2)
                   , qualifiers = qualifiers gs1 ++ qualifiers gs2}

lookupAssertGS :: G2.Name -> GeneratedSpecs -> Maybe [PolyBound Expr]
lookupAssertGS n = M.lookup (zeroOutUnq n) . assert_specs

filterOutSpecs :: [G2.Name] -> GeneratedSpecs -> GeneratedSpecs
filterOutSpecs ns gs =
    let
        ns' = map zeroOutUnq ns
        fil = M.filterWithKey (\n _ -> n `notElem` ns')
    in
    gs { assert_specs = fil $ assert_specs gs
       , assume_specs = fil $ assume_specs gs }

filterOutAssertSpecs :: [G2.Name] -> GeneratedSpecs -> GeneratedSpecs
filterOutAssertSpecs ns gs =
    let
        ns' = map zeroOutUnq ns
        fil = M.filterWithKey (\n _ -> n `notElem` ns')
    in
    gs { assert_specs = fil $ assert_specs gs }


filterAssertsKey :: (G2.Name -> Bool) -> GeneratedSpecs -> GeneratedSpecs
filterAssertsKey p gs = gs { assert_specs = M.filterWithKey (\n _ -> p n) $ assert_specs gs}

deleteAssume :: G2.Name -> GeneratedSpecs -> GeneratedSpecs
deleteAssume n gs@(GeneratedSpecs { assume_specs = as }) =
    gs { assume_specs = M.delete (zeroOutUnq n) as }

deleteAssert :: G2.Name -> GeneratedSpecs -> GeneratedSpecs
deleteAssert n gs@(GeneratedSpecs { assert_specs = as }) =
    gs { assert_specs = M.delete (zeroOutUnq n) as }

deleteAllAssumes :: GeneratedSpecs -> GeneratedSpecs
deleteAllAssumes gs = gs { assume_specs = M.empty }

deleteAllAsserts :: GeneratedSpecs -> GeneratedSpecs
deleteAllAsserts gs = gs { assert_specs = M.empty }

modifyGsTySigs :: (Var -> SpecType -> SpecType) -> GhcInfo -> GhcInfo
modifyGsTySigs f ghci =
    let
        sigs = getTySigs ghci
        sigs' = map (\(v, lst) -> (v, fmap (f v) lst)) sigs
    in
    putTySigs ghci sigs'

modifyGsAsmSigs :: (Var -> SpecType -> SpecType) -> GhcInfo -> GhcInfo
modifyGsAsmSigs f ghci =
    let
        sigs = getAssumedSigs ghci
        sigs' = map (\(v, lst) -> (v, fmap (f v) lst)) sigs
    in
    putAssumedSigs ghci sigs'

addSpecsToGhcInfos :: [GhcInfo] -> GeneratedSpecs -> [GhcInfo]
addSpecsToGhcInfos ghci gs = addAssumedSpecsToGhcInfos (addAssertedSpecsToGhcInfos ghci gs) gs

addAssertedSpecsToGhcInfos :: [GhcInfo] -> GeneratedSpecs -> [GhcInfo]
addAssertedSpecsToGhcInfos ghcis = foldr (uncurry addAssertedSpecToGhcInfos) ghcis
                                 . filter (not . allEmptyPAnds . snd)
                                 . M.toList
                                 . assert_specs

addAssertedSpecToGhcInfos :: G2.Name -> [PolyBound Expr] -> [GhcInfo] -> [GhcInfo]
addAssertedSpecToGhcInfos v e = map (addAssertedSpecToGhcInfo v e) . insertMissingAssertSpec v

addAssertedSpecToGhcInfo :: G2.Name -> [PolyBound Expr] -> GhcInfo -> GhcInfo
addAssertedSpecToGhcInfo n e =
    modifyGsTySigs (\v st -> if varEqName v n then addToSpecType e st else st)

addAssumedSpecsToGhcInfos :: [GhcInfo] -> GeneratedSpecs -> [GhcInfo]
addAssumedSpecsToGhcInfos ghcis = foldr (uncurry addAssumedSpecToGhcInfos) ghcis . M.toList . assume_specs

addAssumedSpecToGhcInfos :: G2.Name -> [PolyBound Expr] -> [GhcInfo] -> [GhcInfo]
addAssumedSpecToGhcInfos v e = map (addAssumedSpecToGhcInfo v e) . insertMissingAssumeSpec v

addAssumedSpecToGhcInfo :: G2.Name -> [PolyBound Expr] -> GhcInfo -> GhcInfo
addAssumedSpecToGhcInfo n e =
    modifyGsAsmSigs (\v st -> if varEqName v n then addToSpecType e st else st)

addQualifiersToGhcInfos :: GeneratedSpecs -> [GhcInfo] -> [GhcInfo]
addQualifiersToGhcInfos gs = map (addQualifiersToGhcInfo gs)

addQualifiersToGhcInfo :: GeneratedSpecs -> GhcInfo -> GhcInfo
addQualifiersToGhcInfo gs ghci =
    let
        old_quals = getQualifiers ghci
    in
    putQualifiers ghci (old_quals ++ qualifiers gs)

addToSpecType :: [PolyBound Expr] -> SpecType -> SpecType
addToSpecType _ rvar@(RVar {}) = rvar
addToSpecType ees@(e@(PolyBound _ ps):es) rfun@(RFun { rt_in = i, rt_out = out })
    | isFunTy i = rfun { rt_in = addToSpecType ps i, rt_out = addToSpecType es out }
    | not (isRVar i) = rfun { rt_in = addToSpecType [e] i, rt_out = addToSpecType es out }
    | otherwise = rfun {rt_out = addToSpecType ees out }
addToSpecType es rall@(RAllT { rt_ty = out }) =
    rall { rt_ty = addToSpecType es out }
addToSpecType [PolyBound e ps]
        rapp@(RApp { rt_reft = u@(MkUReft { ur_reft = Reft (ur_s, ur_e) }), rt_args = ars }) =
    let
        rt_reft' = u { ur_reft = Reft (ur_s, PAnd [ur_e, e])}
        ars' = map (uncurry addToSpecType) $ zipSpecTypes (map (:[]) ps) ars
    in
    rapp { rt_reft = rt_reft', rt_args = ars' }
addToSpecType [] st = st
addToSpecType _ st = error $ "addToSpecType: Unhandled SpecType " ++ show st

zipSpecTypes :: [[PolyBound Expr]] -> [SpecType] -> [([PolyBound Expr], SpecType)]
zipSpecTypes [] [] = []
zipSpecTypes (epb:epbs) (rfun@(RFun {}):sts) =
    (epb, rfun):zipSpecTypes epbs sts
zipSpecTypes epbs (rvar@(RVar {}):sts) =
    ([PolyBound PTrue []], rvar):zipSpecTypes epbs sts
zipSpecTypes (epb:epbs) (st@(RApp {}):sts) = (epb, st):zipSpecTypes epbs sts
zipSpecTypes [] (st:sts) = ([PolyBound PTrue []], st):zipSpecTypes [] sts
zipSpecTypes es st = error $ "zipSpecTypes: Unhandled case\n" ++ show es ++ "\n" ++ show st

zeroOutUnq :: G2.Name -> G2.Name
zeroOutUnq (G2.Name n m _ l) = G2.Name n m 0 l

allEmptyPAnds :: [PolyBound Expr] -> Bool
allEmptyPAnds = all (allPB (\e -> case e of
                                      PAnd [] -> True
                                      _ -> False))

-- | If the given variable does not have a specification, create it in the appropriate place
insertMissingAssumeSpec :: G2.Name -> [GhcInfo] -> [GhcInfo]
insertMissingAssumeSpec (G2.Name n _ _ _) = map create 
    where
        create ghci =
            let
                defs = definedVars ghci
                has_spec = map fst $ getAssumedSigs ghci
                def_no_spec = filter (`notElem` has_spec) defs

                def_v = find (\v -> (T.pack . occNameString . nameOccName $ varName v) == n) def_no_spec
            in
            case def_v of
                Just v ->
                    let
                        new_spec = dummyLoc $ genSpec' ghci v
                    in
                    insertAssumeSig v new_spec ghci
                Nothing -> ghci

insertAssumeSig :: Var -> LocSpecType -> GhcInfo -> GhcInfo
insertAssumeSig v lst ghci =
    let
        spc = getAssumedSigs ghci
    in
    putAssumedSigs ghci ((v, lst):spc)

insertMissingAssertSpec :: G2.Name -> [GhcInfo] -> [GhcInfo]
insertMissingAssertSpec (G2.Name n _ _ _) = map create
    where
        create ghci =
            let
                defs = definedVars ghci
                has_spec = map fst $ getTySigs ghci
                def_no_spec = filter (`notElem` has_spec) defs

                def_v = find (\v -> (T.pack . occNameString . nameOccName $ varName v) == n) def_no_spec
            in
            case def_v of
                Just v ->
                    let
                        new_spec = dummyLoc $ genSpec' ghci v
                    in
                    insertTySig v new_spec ghci
                Nothing -> ghci

insertTySig :: Var -> LocSpecType -> GhcInfo -> GhcInfo
insertTySig v lst ghci =
    let
        spc = getTySigs ghci
    in
    putTySigs ghci ((v, lst):spc)

allExprs :: GeneratedSpecs -> [Expr]
allExprs gs = concatMap extractValues . concat $ M.elems (assume_specs gs) ++ M.elems (assert_specs gs)

genSpec :: [GhcInfo] -> G2.Name -> Maybe SpecType
genSpec ghcis (G2.Name n _ _ _) = foldr mappend Nothing $ map gen ghcis
    where
        gen ghci =
            let
                defs = definedVars ghci
                def_v = find (\v -> (T.pack . occNameString . nameOccName $ varName v) == n) defs

                specs = getTySigs ghci
            in
            case def_v of
                Just v
                    | Just (_, s) <- find ((==) v . fst) specs -> Just (val s)
                _ -> fmap (genSpec' ghci) def_v

genSpec' :: GhcInfo -> Var -> SpecType
genSpec' ghci v =
    S.evalState (refreshTy (ofType $ varType v)) $ initCGI (getConfig ghci) ghci

definedVars :: GhcInfo -> [Var]
#if MIN_VERSION_liquidhaskell(0,8,6)
definedVars = giDefVars . giSrc
#else
definedVars = defVars
#endif


