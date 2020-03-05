module G2.Liquid.Inference.GeneratedSpecs ( GeneratedSpecs
                                          , emptyGS

                                          , nullAssumeGS

                                          , insertAssumeGS
                                          , insertAssertGS
                                          , insertQualifier
                                          , switchAssumesToAsserts

                                          , filterAssertsKey

                                          , addSpecsToGhcInfos
                                          , addAssumedSpecsToGhcInfos
                                          , addQualifiersToGhcInfos
                                          , deleteAssert
                                          , deleteAllAssumes
                                          , deleteAllAsserts

                                          , genSpec
                                          , insertMissingAssertSpec ) where

import qualified G2.Language as G2
import G2.Liquid.Helpers
import G2.Liquid.Inference.PolyRef

import Language.Haskell.Liquid.Constraint.Init
import Language.Haskell.Liquid.Types
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

insertAssumeGS :: G2.Name -> [PolyBound Expr] -> GeneratedSpecs -> GeneratedSpecs
insertAssumeGS n e gs =
    gs { assume_specs = M.insert (zeroOutUnq n) e (assume_specs gs) }

insertAssertGS :: G2.Name -> [PolyBound Expr] -> GeneratedSpecs -> GeneratedSpecs
insertAssertGS n e gs =
    gs { assert_specs = M.insert (zeroOutUnq n) e (assert_specs gs) }

insertQualifier :: Qualifier -> GeneratedSpecs -> GeneratedSpecs
insertQualifier qual gs@(GeneratedSpecs { qualifiers = quals }) =
    gs { qualifiers = qual:quals }

switchAssumesToAsserts :: GeneratedSpecs -> GeneratedSpecs
switchAssumesToAsserts gs =
    gs { assert_specs =
            M.unionWith
                (zipWith
                    (zipWithMaybePB (\s1 s2 -> PAnd [maybe PTrue id s1, maybe PTrue id s2]))
                )
                (assert_specs gs) (assume_specs gs)
       , assume_specs = M.empty }

filterAssertsKey :: (G2.Name -> Bool) -> GeneratedSpecs -> GeneratedSpecs
filterAssertsKey p gs = gs { assert_specs = M.filterWithKey (\n _ -> p n) $ assert_specs gs}

deleteAssert :: G2.Name -> GeneratedSpecs -> GeneratedSpecs
deleteAssert n gs@(GeneratedSpecs { assert_specs = as }) =
    gs { assert_specs = M.delete n as }

deleteAllAssumes :: GeneratedSpecs -> GeneratedSpecs
deleteAllAssumes gs = gs { assume_specs = M.empty }

deleteAllAsserts :: GeneratedSpecs -> GeneratedSpecs
deleteAllAsserts gs = gs { assert_specs = M.empty }

modifyGsTySigs :: (Var -> SpecType -> SpecType) -> GhcInfo -> GhcInfo
modifyGsTySigs f gi@(GI { spec = si@(SP { gsTySigs = tySigs }) }) =
    gi { spec = si { gsTySigs = map (\(v, lst) -> (v, fmap (f v) lst)) tySigs }}

modifyGsAsmSigs :: (Var -> SpecType -> SpecType) -> GhcInfo -> GhcInfo
modifyGsAsmSigs f gi@(GI { spec = si@(SP { gsAsmSigs = tySigs }) }) =
    gi { spec = si { gsAsmSigs = map (\(v, lst) -> (v, fmap (f v) lst)) tySigs }}

addSpecsToGhcInfos :: [GhcInfo] -> GeneratedSpecs -> [GhcInfo]
addSpecsToGhcInfos ghci gs = addAssumedSpecsToGhcInfos (addAssertedSpecsToGhcInfos ghci gs) gs

addAssertedSpecsToGhcInfos :: [GhcInfo] -> GeneratedSpecs -> [GhcInfo]
addAssertedSpecsToGhcInfos ghcis = foldr (uncurry addAssertedSpecToGhcInfos) ghcis . M.toList . assert_specs

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
addQualifiersToGhcInfo gs ghci@(GI { spec = sp@(SP { gsQualifiers = quals' })}) =
    ghci { spec = sp { gsQualifiers = qualifiers gs ++ quals' }}

addToSpecType :: [PolyBound Expr] -> SpecType -> SpecType
addToSpecType ees@(e:es) rfun@(RFun { rt_in = i, rt_out = out })
    | not (isFunTy i) && not (isRVar i) = rfun { rt_in = addToSpecType [e] i, rt_out = addToSpecType es out }
    | otherwise = rfun {rt_out = addToSpecType ees out }
addToSpecType es rall@(RAllT { rt_ty = out }) =
    rall { rt_ty = addToSpecType es out }
addToSpecType [PolyBound e ps]
        rapp@(RApp { rt_reft = u@(MkUReft { ur_reft = Reft (ur_s, ur_e) }), rt_args = ars }) =
    let
        rt_reft' = u { ur_reft = Reft (ur_s, PAnd [ur_e, e])}
        
        -- The PolyBound will be missing refinements if there are nested
        -- polymorphic arguments that are never instantiated.  For instance,
        -- if the type is [[Int]], and we only have values of [] :: [[Int]]
        ps' = ps ++ repeat (PolyBound PTrue [])
        ars' = map (uncurry addToSpecType) $ zip (map (:[]) ps') ars
    in
    rapp { rt_reft = rt_reft', rt_args = ars' }
addToSpecType _ rvar@(RVar {}) = rvar
addToSpecType [] st = st
addToSpecType _ st = error $ "addToSpecType: Unhandled SpecType " ++ show st

zeroOutUnq :: G2.Name -> G2.Name
zeroOutUnq (G2.Name n m _ l) = G2.Name n m 0 l

-- | If the given variable does not have a specification, create it in the appropriate place
insertMissingAssumeSpec :: G2.Name -> [GhcInfo] -> [GhcInfo]
insertMissingAssumeSpec (G2.Name n _ _ _) = map create 
    where
        create ghci@(GI { spec = spc } ) =
            let
                defs = defVars ghci
                has_spec = map fst . gsAsmSigs $ spec ghci
                def_no_spec = filter (`notElem` has_spec) defs

                def_v = find (\v -> (T.pack . occNameString . nameOccName $ varName v) == n) def_no_spec
            in
            case def_v of
                Just v ->
                    let
                        new_spec = dummyLoc $ genSpec' ghci v
                    in
                    ghci { spec = spc { gsAsmSigs = (v, new_spec):gsAsmSigs spc } }
                Nothing -> ghci


insertMissingAssertSpec :: G2.Name -> [GhcInfo] -> [GhcInfo]
insertMissingAssertSpec (G2.Name n _ _ _) = map create 
    where
        create ghci@(GI { spec = spc } ) =
            let
                defs = defVars ghci
                has_spec = map fst . gsTySigs $ spec ghci
                def_no_spec = filter (`notElem` has_spec) defs

                def_v = find (\v -> (T.pack . occNameString . nameOccName $ varName v) == n) def_no_spec
            in
            case def_v of
                Just v ->
                    let
                        new_spec = dummyLoc $ genSpec' ghci v
                    in
                    ghci { spec = spc { gsTySigs = (v, new_spec):gsTySigs spc } }
                Nothing -> ghci

genSpec :: [GhcInfo] -> G2.Name -> Maybe SpecType
genSpec ghcis (G2.Name n _ _ _) = foldr mappend Nothing $ map gen ghcis
    where
        gen ghci =
            let
                defs = defVars ghci
                def_v = find (\v -> (T.pack . occNameString . nameOccName $ varName v) == n) defs

                specs = gsTySigs (spec ghci)
            in
            case def_v of
                Just v
                    | Just (_, s) <- find ((==) v . fst) specs -> Just (val s)
                _ -> fmap (genSpec' ghci) def_v

genSpec' :: GhcInfo -> Var -> SpecType
genSpec' ghci v =
    S.evalState (refreshTy (ofType $ varType v)) $ initCGI (getConfig ghci) ghci
