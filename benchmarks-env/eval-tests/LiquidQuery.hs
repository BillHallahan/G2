module LiquidQuery where

import Control.Exception
import Data.Coerce

import Name
import OccName
import Var
import Language.Haskell.Liquid.UX.CmdLine
import Language.Haskell.Liquid.Types
import Language.Fixpoint.Types.Refinements as R
import Language.Fixpoint.Types.Names

import G2.Internals.Liquid.Interface
import G2.Internals.Liquid.Types

import Debug.Trace

lhDir = "/home/celery/foo/yale/G2/benchmarks-env/liquidhaskell-study/wi15/"

lhLibs = map (\f -> lhDir ++ f) ["List.lhs"]

data SpecTypesCompareFlag =
    SpecTypesDiffer
  | SpecTypesSame
  deriving (Eq, Show)

exprFromURef :: RReft -> R.Expr
exprFromURef rreft = snd $ unpackReft $ ur_reft rreft

unpackReft :: Reft -> (Symbol, R.Expr)
unpackReft = coerce

-- CALL THIS
-- Compare var1 in file1's spec type against var1 in file2
structEqFiles ::
  (String, String)
    -> (String, String)
    -> IO (Either SomeException SpecTypesCompareFlag)
structEqFiles pair1 pair2 =
  try $ structEqSpecTypesFromFiles pair1 pair2 lhDir lhLibs

structEqSpecTypesFromFiles ::
  (String, String) -> (String, String) -> String -> [String]
    -> IO SpecTypesCompareFlag
structEqSpecTypesFromFiles (var1, file1) (var2, file2) proj lhlibs = do
  mbSty1 <- getVarFileSpecTypes var1 file1 proj lhlibs
  mbSty2 <- getVarFileSpecTypes var2 file2 proj lhlibs
  case (mbSty1, mbSty2) of
    (Just sty1, Just sty2) ->
      if specTypesStructEq sty1 sty2
        then return SpecTypesSame
        else return SpecTypesDiffer
    (Nothing, Nothing) -> return SpecTypesSame
    (_, Nothing) -> return SpecTypesDiffer
    (Nothing, _) -> return SpecTypesDiffer

getVarFileSpecTypes ::
  String -> String -> String -> [String]-> IO (Maybe SpecType)
getVarFileSpecTypes var file proj lhlibs = do
  varStys <- getVarSpecTypes file proj lhlibs
  return $ findSpecType var varStys

getVarSpecTypes :: String -> String -> [String] -> IO [(Var, SpecType)]
getVarSpecTypes file proj lhlibs = do
  lhConfig <- getOpts []
  lhOuts <- getGHCInfos lhConfig proj [file] lhlibs
  return $ map (\(a, b) -> (a, val b)) $ funcSpecs $ map ghcI lhOuts

findSpecType :: String -> [(Var, SpecType)] -> Maybe SpecType
findSpecType _ [] = Nothing
findSpecType name ((v, sty) : stys) =
  if name == (occNameString $ nameOccName $ Var.varName v)
    then Just sty
    else findSpecType name stys

specTypesStructEq :: SpecType -> SpecType -> Bool
specTypesStructEq
  (RVar {rt_var = rtv1, rt_reft = ref1})
  (RVar {rt_var = rtv2, rt_reft = ref2})
    =
      -- trace ("stvar " ++ show (rtv2, ref2) $
      refTypesEq (exprFromURef ref1) (exprFromURef ref2)
specTypesStructEq
  (RFun {rt_bind = rb1, rt_in = rin1, rt_out = rout1, rt_reft = ref1})
  (RFun {rt_bind = rb2, rt_in = rin2, rt_out = rout2, rt_reft = ref2})
    =
      -- trace ("stfun " ++ show (ref2) $
      specTypesStructEq rin1 rin2 &&
      specTypesStructEq rout1 rout2 &&
      refTypesEq (exprFromURef ref1) (exprFromURef ref2)
specTypesStructEq
  (RAllT {rt_tvbind = rtb1, rt_ty = rty1})
  (RAllT {rt_tvbind = rtb2, rt_ty = rty2})
    =
      -- trace ("strtall " ++ show (rty2) $
      specTypesStructEq rty1 rty2
specTypesStructEq
  (RApp {rt_tycon = rtc1, rt_args = rta1, rt_pargs = rtpa1, rt_reft = ref1})
  (RApp {rt_tycon = rtc2, rt_args = rta2, rt_pargs = rtpa2, rt_reft = ref2})
    =
      -- trace ("strapp " ++ show (ref1, ref2, refTypesEq (exprFromURef ref1) (exprFromURef ref2)) $
      refTypesEq (exprFromURef ref1) (exprFromURef ref2) &&
      (length rta1 == length rta2) &&
      (all id $ map (uncurry specTypesStructEq) $ zip rta1 rta2)
specTypesStructEq
  (RAppTy {rt_arg = rta1, rt_res = res1, rt_reft = ref1})
  (RAppTy {rt_arg = rta2, rt_res = res2, rt_reft = ref2})
    = specTypesStructEq rta1 rta2 &&
      refTypesEq (exprFromURef ref1) (exprFromURef ref2)

specTypesStructEq (RVar {}) sty2 = False
specTypesStructEq (RFun {}) sty2 = False
specTypesStructEq (RAllT {}) sty2 = False
specTypesStructEq (RApp {}) sty2 = False
specTypesStructEq (RAppTy {}) sty2 = False

specTypesStructEq sty1 sty2 =
  -- trace ("specTypesStructEq: catch all") $
  True


refTypesEq :: R.Expr -> R.Expr -> Bool
refTypesEq (ECon c1) (ECon c2) =
  -- trace "rfecon" $
  c1 == c2
refTypesEq (EVar v1) (EVar v2) =
  -- trace "rfevar" $
  True
refTypesEq (EApp ef1 ea1) (EApp ef2 ea2) =
  -- trace "rfeapp" $
  refTypesEq ef1 ef2 && refTypesEq ea1 ea2
refTypesEq (ENeg e1) (ENeg e2) =
  -- trace "rfeneg" $
  refTypesEq e1 e2
refTypesEq (EBin b1 ep1 eq1) (EBin b2 ep2 eq2) =
  -- trace "rfebin" $
  b1 == b2 && refTypesEq ep1 ep2 && refTypesEq eq1 eq2
refTypesEq (ECst e1 s1) (ECst e2 s2) =
  -- trace "rfecst" $
  refTypesEq e1 e2
refTypesEq (PAnd es1) (PAnd es2) =
  -- trace "rfeand" $
  (length es1 == length es2) && (all id $ map (uncurry refTypesEq) $ zip es1 es2)
refTypesEq (POr es1) (POr es2) =
  -- trace "rfeor" $
  (length es1 == length es2) && (all id $ map (uncurry refTypesEq) $ zip es1 es2)
refTypesEq (PNot e1) (PNot e2) =
  -- trace "rfenot" $
  refTypesEq e1 e2
refTypesEq (PImp ep1 eq1) (PImp ep2 eq2) =
  -- trace "rfeimp" $
  refTypesEq ep1 ep2 && refTypesEq eq1 eq2
refTypesEq (PIff ep1 eq1) (PIff ep2 eq2) =
  -- trace "rfeiff" $
  refTypesEq ep1 ep2 && refTypesEq eq1 eq2
refTypesEq (PAtom bre1 ep1 eq1) (PAtom bre2 ep2 eq2) =
  -- trace ("rfpatom " ++ show (bre1, bre2)) $
  bre1 == bre2 && refTypesEq ep1 ep2 && refTypesEq eq1 eq2
refTypesEq _ _ = False





