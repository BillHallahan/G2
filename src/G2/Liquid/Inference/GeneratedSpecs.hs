module G2.Liquid.Inference.GeneratedSpecs ( GeneratedSpecs
                                          , emptyGS
                                          , nullAssumeGS
                                          , insertAssumeGS
                                          , insertQualifier
                                          , switchAssumesToAsserts
                                          , addSpecsToGhcInfos
                                          , addQualifiersToGhcInfos
                                          , deleteAssert ) where

import qualified G2.Language as G2
import G2.Liquid.Helpers
import G2.Liquid.Inference.PolyRef

import Language.Haskell.Liquid.Types
import Language.Fixpoint.Types.Refinements
import Language.Fixpoint.Types

import Data.Coerce
import qualified Data.Map as M

import Var

import Debug.Trace

data GeneratedSpecs = GeneratedSpecs { assert_specs :: M.Map G2.Name (PolyBound Expr)
                                     , assume_specs :: M.Map G2.Name (PolyBound Expr)
                                     , qualifiers :: [Qualifier] } deriving (Eq, Show)

emptyGS :: GeneratedSpecs
emptyGS = GeneratedSpecs M.empty M.empty []

nullAssumeGS :: GeneratedSpecs -> Bool
nullAssumeGS = M.null . assume_specs

insertAssumeGS :: G2.Name -> PolyBound Expr -> GeneratedSpecs -> GeneratedSpecs
insertAssumeGS n e gs =
    gs { assume_specs = M.insert (zeroOutUnq n) e (assume_specs gs) }

insertQualifier :: Qualifier -> GeneratedSpecs -> GeneratedSpecs
insertQualifier qual gs@(GeneratedSpecs { qualifiers = quals }) =
    gs { qualifiers = qual:quals }

switchAssumesToAsserts :: GeneratedSpecs -> GeneratedSpecs
switchAssumesToAsserts gs =
    gs { assert_specs =
            M.unionWith
                (zipWithMaybePB (\s1 s2 -> PAnd [maybe PTrue id s1, maybe PTrue id s2]))
                (assert_specs gs) (assume_specs gs)
       , assume_specs = M.empty }

deleteAssert :: G2.Name -> GeneratedSpecs -> GeneratedSpecs
deleteAssert n gs@(GeneratedSpecs { assert_specs = as }) =
    gs { assert_specs = M.delete n as }

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

addAssertedSpecToGhcInfos :: G2.Name -> PolyBound Expr -> [GhcInfo] -> [GhcInfo]
addAssertedSpecToGhcInfos v e = map (addAssertedSpecToGhcInfo v e)

addAssertedSpecToGhcInfo :: G2.Name -> PolyBound Expr -> GhcInfo -> GhcInfo
addAssertedSpecToGhcInfo n e =
    modifyGsTySigs (\v st -> if varEqName v n then addPost e st else st)

addAssumedSpecsToGhcInfos :: [GhcInfo] -> GeneratedSpecs -> [GhcInfo]
addAssumedSpecsToGhcInfos ghcis = foldr (uncurry addAssumedSpecToGhcInfos) ghcis . M.toList . assert_specs

addAssumedSpecToGhcInfos :: G2.Name -> PolyBound Expr -> [GhcInfo] -> [GhcInfo]
addAssumedSpecToGhcInfos v e = map (addAssumedSpecToGhcInfo v e)

addAssumedSpecToGhcInfo :: G2.Name -> PolyBound Expr -> GhcInfo -> GhcInfo
addAssumedSpecToGhcInfo n e =
    modifyGsAsmSigs (\v st -> if varEqName v n then addPost e st else st)

addQualifiersToGhcInfos :: GeneratedSpecs -> [GhcInfo] -> [GhcInfo]
addQualifiersToGhcInfos gs = map (addQualifiersToGhcInfo gs)

addQualifiersToGhcInfo :: GeneratedSpecs -> GhcInfo -> GhcInfo
addQualifiersToGhcInfo gs ghci@(GI { spec = sp@(SP { gsQualifiers = quals' })}) =
    ghci { spec = sp { gsQualifiers = qualifiers gs ++ quals' }}

addPost :: PolyBound Expr -> SpecType -> SpecType
addPost e rfun@(RFun { rt_out = out }) = rfun { rt_out = addPost e out }
addPost e rall@(RAllT { rt_ty = out }) =
    rall { rt_ty = addPost e out }
addPost (PolyBound e ps)
        rapp@(RApp { rt_reft = u@(MkUReft { ur_reft = Reft (ur_s, ur_e) }), rt_args = ars }) =
    let
        rt_reft' = u { ur_reft = Reft (ur_s, PAnd [ur_e, e])}
        
        -- The PolyBound will be missing refinements if there are nested
        -- polymorphic arguments that are never instantiated.  For instance,
        -- if the type is [[Int]], and we only have values of [] :: [[Int]]
        ps' = ps ++ repeat (PolyBound PTrue [])
        ars' = map (uncurry addPost) $ zip ps' ars
    in
    rapp { rt_reft = rt_reft', rt_args = ars' }
addPost _ rvar@(RVar {}) = rvar
addPost _ st = error $ "addPost: Unhandled SpecType " ++ show st

zeroOutUnq :: G2.Name -> G2.Name
zeroOutUnq (G2.Name n m _ l) = G2.Name n m 0 l