module G2.Liquid.Inference.Interface (inference) where

import G2.Config.Config as G2
import G2.Language.Naming
import G2.Language.Syntax
import G2.Liquid.Inference.FuncConstraint
import G2.Liquid.Inference.RefSynth
import G2.Liquid.Inference.Verify
import G2.Liquid.Interface
import G2.Liquid.Types
import G2.Translation

import Language.Fixpoint.Types.Constraints
import Language.Haskell.Liquid.Types as LH

import qualified Data.Text as T

inference :: G2.Config -> [FilePath] -> [FilePath] -> [FilePath] -> IO ()
inference config proj fp lhlibs = do
    -- Initialize LiquidHaskell
    lhconfig <- lhConfig proj lhlibs
    ghci <- ghcInfos Nothing lhconfig fp

    -- Initialize G2
    let g2config = config { mode = Liquid, steps = 2000 }
    exg2 <- translateLoaded proj fp lhlibs (simplTranslationConfig { simpl = False }) g2config

    inference' g2config lhconfig ghci exg2 emptyFC 

inference' :: G2.Config -> LH.Config -> [GhcInfo] -> (Maybe T.Text, ExtractedG2) -> FuncConstraints -> IO ()
inference' g2config lhconfig ghci exg2 fc = do
    res <- verify lhconfig ghci

    case res of
        Safe -> putStrLn "Safe"
        Crash -> putStrLn "Crash"
        Unsafe bad -> do
            print bad
            let bad' = map nameOcc bad

            print $ fst exg2

            res <- mapM (\n -> do
                ((exec_res, _), i) <- runLHCore n exg2 ghci g2config
                return $ map (lhStateToCE i) exec_res) bad'

            let new_fc = concatMap genFuncConstraints $ concat res
                new_fc_funcs = map (funcName . constraint) new_fc

                fc' = foldr insertFC fc new_fc

            mapM (refSynth . flip lookupFC fc') new_fc_funcs

            return ()
 
genFuncConstraints :: CounterExample -> [FuncConstraint]
genFuncConstraints (PostCounter _ fcs@(_:_)) = map Neg fcs