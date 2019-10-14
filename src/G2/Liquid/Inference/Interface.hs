module G2.Liquid.Inference.Interface (inference) where

import G2.Config.Config as G2
import G2.Language.Naming
import G2.Language.Syntax
import G2.Liquid.Inference.CheckCounterexample
import G2.Liquid.Inference.FuncConstraint
import G2.Liquid.Helpers
import G2.Liquid.Inference.RefSynth
import G2.Liquid.Inference.GeneratedSpecs
import G2.Liquid.Inference.Verify
import G2.Liquid.Interface
import G2.Liquid.Types
import G2.Translation

import Language.Fixpoint.Types.Constraints
import Language.Haskell.Liquid.Types as LH

import Data.Maybe
import qualified Data.Text as T

inference :: G2.Config -> [FilePath] -> [FilePath] -> [FilePath] -> IO ()
inference config proj fp lhlibs = do
    -- Initialize LiquidHaskell
    lhconfig <- lhConfig proj lhlibs
    let lhconfig' = lhconfig { pruneUnsorted = True }
    ghci <- ghcInfos Nothing lhconfig' fp

    -- Initialize G2
    let g2config = config { mode = Liquid, steps = 2000 }
    exg2 <- translateLoaded proj fp lhlibs (simplTranslationConfig { simpl = False }) g2config

    inference' g2config lhconfig' ghci exg2 emptyGS emptyFC 

inference' :: G2.Config -> LH.Config -> [GhcInfo] -> (Maybe T.Text, ExtractedG2) -> GeneratedSpecs -> FuncConstraints -> IO ()
inference' g2config lhconfig ghci exg2 gs fc = do
    print gs

    let merged_ghci = addSpecsToGhcInfos ghci gs
    mapM_ (print . gsTySigs . spec) merged_ghci

    res <- verify lhconfig merged_ghci

    case res of
        Safe -> putStrLn "Safe"
        Crash -> putStrLn "Crash"
        Unsafe bad -> do
            -- Generate constraints
            let bad' = map nameOcc bad

            putStrLn $ "bad' = " ++ show bad'

            res <- mapM (\n -> do
                ((exec_res, _), i) <- runLHCore n exg2 merged_ghci g2config
                return $ map (lhStateToCE i) exec_res) bad'

            new_fc <- return . concat =<< mapM (cexsToFuncConstraints exg2 ghci g2config) (concat res)
            let new_fc_funcs = map (funcName . constraint) new_fc

                fc' = foldr insertFC fc new_fc

            -- Synthesize
            new_exprs <- mapM 
                        (\n -> do
                            let fc_of_n = lookupFC n fc'
                                spec = fromJust $ findFuncSpec ghci n
                            new_spec <- refSynth spec fc_of_n

                            putStrLn $ "spec = " ++ show spec
                            putStrLn $ "new_spec = " ++ show new_spec

                            return (n, new_spec)) new_fc_funcs

            let gs' = foldr (uncurry insertGS) gs new_exprs
            
            inference' g2config lhconfig ghci exg2 gs' fc'


cexsToFuncConstraints :: (Maybe T.Text, ExtractedG2) -> [GhcInfo] -> G2.Config -> CounterExample -> IO [FuncConstraint]
cexsToFuncConstraints _ _ _ (DirectCounter _ fcs@(_:_)) = return $ map Neg fcs
cexsToFuncConstraints _ _ _ (CallsCounter _ _ fcs@(_:_)) = return $ map Neg fcs
cexsToFuncConstraints exg2 ghci g2config (DirectCounter fc []) = do
    v_cex <- checkCounterexample exg2 ghci g2config fc
    case v_cex of
        True -> return [Pos fc]
        False -> error "Counterexample to original Spec"
cexsToFuncConstraints exg2 ghci g2config (CallsCounter _ fc []) = do
    v_cex <- checkCounterexample exg2 ghci g2config fc
    case v_cex of
        True -> return [Pos fc]
        False -> error "Counterexample to original Spec"
