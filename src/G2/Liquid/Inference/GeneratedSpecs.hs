module G2.Liquid.Inference.GeneratedSpecs ( GeneratedSpecs
                                          , emptyGS
                                          , insertGS
                                          , addSpecsToGhcInfos ) where

import qualified G2.Language as G2
import G2.Liquid.Helpers

import Language.Haskell.Liquid.Types
import Language.Fixpoint.Types.Refinements
import Language.Fixpoint.Types

import Data.Coerce
import qualified Data.Map as M

import Var

newtype GeneratedSpecs = GeneratedSpecs (M.Map G2.Name Expr) deriving (Eq, Show)

emptyGS :: GeneratedSpecs
emptyGS = GeneratedSpecs M.empty

insertGS :: G2.Name -> Expr -> GeneratedSpecs -> GeneratedSpecs
insertGS n e = coerce . M.insert (zeroOutUnq n) e . coerce

generatedSpecToList :: GeneratedSpecs -> [(G2.Name, Expr)]
generatedSpecToList = M.toList . coerce

modifyGsTySigs :: (Var -> SpecType -> SpecType) -> GhcInfo -> GhcInfo
modifyGsTySigs f gi@(GI { spec = si@(SP { gsTySigs = tySigs }) }) =
    gi { spec = si { gsTySigs = map (\(v, lst) -> (v, fmap (f v) lst)) tySigs }}

addSpecsToGhcInfos :: [GhcInfo] -> GeneratedSpecs -> [GhcInfo]
addSpecsToGhcInfos ghcis = foldr (uncurry addSpecToGhcInfos) ghcis . generatedSpecToList

addSpecToGhcInfos :: G2.Name -> Expr -> [GhcInfo] -> [GhcInfo]
addSpecToGhcInfos v e = map (addSpecToGhcInfo v e)

addSpecToGhcInfo :: G2.Name -> Expr -> GhcInfo -> GhcInfo
addSpecToGhcInfo n e =
    modifyGsTySigs (\v st -> if varEqName v n then addPost e st else st)

addPost :: Expr -> SpecType -> SpecType
addPost e rfun@(RFun { rt_out = out }) = rfun { rt_out = addPost e out }
addPost e rall@(RAllT { rt_ty = out }) =
	rall { rt_ty = addPost e out }
addPost e rapp@(RApp { rt_reft = u@(MkUReft {ur_reft = Reft (ur_s, ur_e) }) }) =
    rapp { rt_reft = u { ur_reft = Reft (ur_s, PAnd [ur_e, e])}}
addPost _ st = error $ "addPost: Unhandled SpecType " ++ show st

zeroOutUnq :: G2.Name -> G2.Name
zeroOutUnq (G2.Name n m _ l) = G2.Name n m 0 l