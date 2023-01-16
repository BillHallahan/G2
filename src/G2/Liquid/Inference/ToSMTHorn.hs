module G2.Liquid.Inference.ToSMTHorn (toSMTHorn) where

import G2.Liquid.Inference.Config
import G2.Liquid.Inference.Verify
import G2.Liquid.Types

import Language.Fixpoint.Types.Environments ( elemsIBindEnv )
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Types
        hiding (TargetInfo (..), TargetSrc (..), TargetSpec (..), GhcSrc (..), GhcSpec (..))

import qualified Data.HashMap.Lazy as HM

toSMTHorn :: InferenceConfig -> Config ->  [GhcInfo] -> IO ()
toSMTHorn infconfig cfg ghci = do
    getFInfo infconfig cfg ghci
    return ()

getFInfo :: InferenceConfig -> Config ->  [GhcInfo] -> IO (F.FInfo Cinfo)
getFInfo infconfig cfg ghci = do
    (_, finfo) <- verify' infconfig cfg ghci
    let senv = F.bs finfo
        wf = F.ws finfo
    putStrLn "hornCons"
    mapM_ hornCons wf
    putStrLn "toHorn"
    let clauses = map (toHorn senv) (HM.elems $ F.cm finfo)
    print clauses
    return finfo

hornCons :: F.WfC Cinfo -> IO ()
hornCons (F.WfC { F.wenv = env, F.wrft = rft, F.winfo = info }) = do
    putStrLn "----"
    print $ elemsIBindEnv env
    print rft
    print info

toHorn :: F.BindEnv -> F.SubC Cinfo -> ([(F.Symbol, F.SortedReft)], F.SortedReft, F.SortedReft)
toHorn bind subC =
    let env = F.senv subC
        lhs = F.slhs subC
        rhs = F.srhs subC
        foralls = filter (not . F.isFunctionSortedReft . snd) $ map (`F.lookupBindEnv` bind) (elemsIBindEnv env)
    in
    (foralls, lhs, rhs)

giInfo :: F.SubC Cinfo -> String
giInfo sc =
  "F.SubC Cinfo " ++ "\n_senv = " ++ show (elemsIBindEnv $ F.senv sc) ++ "\nslhs = " ++ show (F.slhs sc) ++ "\nsrhs = " ++ show (F.srhs sc)
                      ++ "\n_sid = " ++ show (F.sid sc) ++ "\n_stag = " ++ show (F.stag sc) ++ "\n_sinfo = " ++ show (F.sinfo sc)
