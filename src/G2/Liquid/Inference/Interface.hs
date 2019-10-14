module G2.Liquid.Inference.Interface (inference) where

import G2.Config.Config as G2
import G2.Language.Naming
import G2.Language.Syntax
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
    let ghci' = addSpecsToGhcInfos ghci gs
    mapM_ (print . gsTySigs . spec) $ ghci'

    res <- verify lhconfig ghci'

    case res of
        Safe -> putStrLn "Safe"
        Crash -> putStrLn "Crash"
        Unsafe bad -> do
            print bad
            -- Generate constraints
            let bad' = map nameOcc bad

            print $ fst exg2

            res <- mapM (\n -> do
                ((exec_res, _), i) <- runLHCore n exg2 ghci' g2config
                return $ map (lhStateToCE i) exec_res) bad'

            let new_fc = concatMap cexsToFuncConstraints $ concat res
                new_fc_funcs = map (funcName . constraint) new_fc

                fc' = foldr insertFC fc new_fc

            -- Synthesize
            new_exprs <- mapM 
                        (\n -> do
                            let fc_of_n = lookupFC n fc'
                                spec = fromJust $ findFuncSpec ghci n
                            new_spec <- refSynth spec fc_of_n
                            return (n, new_spec)) new_fc_funcs

            let gs' = foldr (uncurry insertGS) gs new_exprs

            print new_exprs
            
            inference' g2config lhconfig ghci exg2 gs' fc'


cexsToFuncConstraints :: CounterExample -> [FuncConstraint]
cexsToFuncConstraints (PostCounter _ fcs@(_:_)) = map Neg fcs