module LiquidQuery where

import Name
import OccName
import Var
import Language.Haskell.Liquid.UX.CmdLine
import Language.Haskell.Liquid.Types

import G2.Internals.Liquid.Interface
import G2.Internals.Liquid.Types

lhDir = "/home/celery/foo/yale/G2/benchmarks-env/liquidhaskell-study/wi15/"

lhLibs = map (\f -> lhDir ++ f) ["List.lhs"]

data SpecTypesCompareFlag =
    SpecTypesDiffer
  | SpecTypesSame
  | SpecTypesNotFound
  deriving (Eq, Show)

-- CALL THIS
-- Compare var1 in file1's spec type against var1 in file2
structDiffFiles ::
  (String, String) -> (String, String) -> IO SpecTypesCompareFlag
structDiffFiles pair1 pair2 =
  structDiffSpecTypesFromFiles pair1 pair2 lhDir lhLibs


structDiffSpecTypesFromFiles ::
  (String, String) -> (String, String) -> String -> [String]
    -> IO SpecTypesCompareFlag
structDiffSpecTypesFromFiles (var1, file1) (var2, file2) proj lhlibs = do
  mbSty1 <- getVarFileSpecTypes var1 file1 proj lhlibs
  mbSty2 <- getVarFileSpecTypes var2 file2 proj lhlibs
  case (mbSty1, mbSty2) of
    (Just sty1, Just sty2) ->
      if specTypesStructDiffer sty1 sty2
        then return SpecTypesDiffer
        else return SpecTypesSame
    _ -> return SpecTypesNotFound


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


specTypesStructDiffer :: SpecType -> SpecType -> Bool
specTypesStructDiffer
  (RVar {rt_var = rtv1, rt_reft = ref1})
  (RVar {rt_var = rtv2, rt_reft = ref2})
    = False
specTypesStructDiffer
  (RFun {rt_bind = rb1, rt_in = rin1, rt_out = rout1, rt_reft = ref1})
  (RFun {rt_bind = rb2, rt_in = rin2, rt_out = rout2, rt_reft = ref2})
    = specTypesStructDiffer rin1 rin2 &&
      specTypesStructDiffer rout1 rout2
specTypesStructDiffer
  (RAllT {rt_tvbind = rtb1, rt_ty = rty1})
  (RAllT {rt_tvbind = rtb2, rt_ty = rty2})
    = specTypesStructDiffer rty1 rty2
specTypesStructDiffer
  (RApp {rt_tycon = rtc1, rt_args = rta1, rt_pargs = rtpa1, rt_reft = ref1})
  (RApp {rt_tycon = rtc2, rt_args = rta2, rt_pargs = rtpa2, rt_reft = ref2})
    = any id $ map (uncurry specTypesStructDiffer) $ zip rta1 rta2
specTypesStructDiffer
  (RAppTy {rt_arg = rta1, rt_res = res1, rt_reft = ref1})
  (RAppTy {rt_arg = rta2, rt_res = res2, rt_reft = ref2})
    = specTypesStructDiffer rta1 rta2

specTypesStructDiffer (RVar {}) sty2 = True
specTypesStructDiffer (RFun {}) sty2 = True
specTypesStructDiffer (RAllT {}) sty2 = True
specTypesStructDiffer (RApp {}) sty2 = True
specTypesStructDiffer (RAppTy {}) sty2 = True

specTypesStructDiffer sty1 sty2 = False



