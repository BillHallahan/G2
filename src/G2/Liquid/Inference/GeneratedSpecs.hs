module G2.Liquid.Inference.GeneratedSpecs ( GeneratedSpecs
                                          , emptyGS
                                          , insertGS
                                          , addSpecsToGhcInfos ) where

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

newtype GeneratedSpecs = GeneratedSpecs (M.Map G2.Name (PolyBound Expr)) deriving (Eq, Show)

emptyGS :: GeneratedSpecs
emptyGS = GeneratedSpecs M.empty

insertGS :: G2.Name -> PolyBound Expr -> GeneratedSpecs -> GeneratedSpecs
insertGS n e = coerce . M.insert (zeroOutUnq n) e . coerce

generatedSpecToList :: GeneratedSpecs -> [(G2.Name, PolyBound Expr)]
generatedSpecToList = M.toList . coerce

modifyGsTySigs :: (Var -> SpecType -> SpecType) -> GhcInfo -> GhcInfo
modifyGsTySigs f gi@(GI { spec = si@(SP { gsTySigs = tySigs }) }) =
    gi { spec = si { gsTySigs = map (\(v, lst) -> (v, fmap (f v) lst)) tySigs }}

addSpecsToGhcInfos :: [GhcInfo] -> GeneratedSpecs -> [GhcInfo]
addSpecsToGhcInfos ghcis = foldr (uncurry addSpecToGhcInfos) ghcis . generatedSpecToList

addSpecToGhcInfos :: G2.Name -> PolyBound Expr -> [GhcInfo] -> [GhcInfo]
addSpecToGhcInfos v e = map (addSpecToGhcInfo v e)

addSpecToGhcInfo :: G2.Name -> PolyBound Expr -> GhcInfo -> GhcInfo
addSpecToGhcInfo n e =
    modifyGsTySigs (\v st -> if varEqName v n then addPost e st else st)

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