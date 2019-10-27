module G2.Liquid.Inference.Interface (inference) where

import G2.Config.Config as G2
import G2.Language.Naming
import G2.Language.Syntax
import G2.Liquid.Inference.FuncConstraint
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Helpers
import G2.Liquid.Inference.RefSynth
import G2.Liquid.Inference.GeneratedSpecs
import G2.Liquid.Inference.Verify
import G2.Liquid.Interface
import G2.Liquid.Types
import G2.Translation

import Language.Fixpoint.Types.Constraints
import Language.Haskell.Liquid.Types as LH

import Control.Monad
import Data.Either
import Data.Maybe
import qualified Data.Text as T

inference :: G2.Config -> [FilePath] -> [FilePath] -> [FilePath] -> IO (Either [CounterExample] GeneratedSpecs)
inference config proj fp lhlibs = do
    -- Initialize LiquidHaskell
    lhconfig <- lhConfig proj lhlibs
    let lhconfig' = lhconfig { pruneUnsorted = True }
    ghci <- ghcInfos Nothing lhconfig' fp

    -- Initialize G2
    let g2config = config { mode = Liquid, steps = 2000 }
        transConfig = simplTranslationConfig { simpl = False }
    exg2 <- translateLoaded proj fp lhlibs transConfig g2config

    inference' g2config lhconfig' ghci exg2 emptyGS emptyFC 

inference' :: G2.Config -> LH.Config -> [GhcInfo] -> (Maybe T.Text, ExtractedG2)
           -> GeneratedSpecs -> FuncConstraints -> IO (Either [CounterExample] GeneratedSpecs)
inference' g2config lhconfig ghci exg2 gs fc = do
    print gs

    let merged_ghci = addSpecsToGhcInfos ghci gs
    mapM_ (print . gsTySigs . spec) merged_ghci

    res <- verify lhconfig merged_ghci

    case res of
        Safe -> return $ Right gs
        Crash -> error "Crash"
        Unsafe bad -> do
            -- Generate constraints
            let bad' = map nameOcc bad

            putStrLn $ "bad' = " ++ show bad'

            res <- mapM (genNewConstraints merged_ghci exg2 g2config) bad'

            new_fc <- checkNewConstraints ghci exg2 g2config (concat res)
            case new_fc of
                Left ce -> return . Left $ ce
                Right new_fc' -> do
                    let new_fc_funcs = map (funcName . constraint) new_fc'

                        fc' = foldr insertFC fc new_fc'

                    -- Synthesize
                    meas_ex <- genMeasureExs exg2 merged_ghci g2config fc'
                    gs' <- foldM (synthesize ghci meas_ex fc') gs new_fc_funcs
                    
                    inference' g2config lhconfig ghci exg2 gs' fc'

genNewConstraints :: [GhcInfo] -> (Maybe T.Text, ExtractedG2) -> G2.Config -> T.Text -> IO [CounterExample]
genNewConstraints ghci exg2 g2config n = do
    ((exec_res, _), i) <- runLHCore n exg2 ghci g2config
    return $ map (lhStateToCE i) exec_res

checkNewConstraints :: [GhcInfo] -> (Maybe T.Text, ExtractedG2) -> G2.Config -> [CounterExample] -> IO (Either [CounterExample] [FuncConstraint])
checkNewConstraints ghci exg2 g2config cexs = do
    res <- mapM (cexsToFuncConstraints exg2 ghci g2config) cexs
    case lefts res of
        res'@(_:_) -> return . Left $ res'
        _ -> return . Right . concat . rights $ res

genMeasureExs :: (Maybe T.Text, ExtractedG2) -> [GhcInfo] -> G2.Config -> FuncConstraints -> IO MeasureExs
genMeasureExs exg2 ghci g2config fcs =
    let
        es = concatMap (\fc -> returns (constraint fc):arguments (constraint fc)) (allFC fcs)
    in
    evalMeasures exg2 ghci g2config es

synthesize :: [GhcInfo] -> MeasureExs -> FuncConstraints -> GeneratedSpecs -> Name -> IO GeneratedSpecs
synthesize ghci meas_ex fc gs n = do
    let fc_of_n = lookupFC n fc
        spec = case findFuncSpec ghci n of
                Just spec' -> spec'
                Nothing -> error $ "No spec found for " ++ show n
    new_spec <- refSynth spec meas_ex fc_of_n

    putStrLn $ "spec = " ++ show spec
    putStrLn $ "new_spec = " ++ show new_spec

    return $ insertGS n new_spec gs

cexsToFuncConstraints :: (Maybe T.Text, ExtractedG2) -> [GhcInfo] -> G2.Config -> CounterExample -> IO (Either CounterExample [FuncConstraint])
cexsToFuncConstraints _ _ _ (DirectCounter _ fcs@(_:_)) = return . Right $ map Neg fcs
cexsToFuncConstraints _ _ _ (CallsCounter _ _ fcs@(_:_)) = return . Right $ map Neg fcs
cexsToFuncConstraints exg2 ghci g2config cex@(DirectCounter fc []) = do
    v_cex <- checkCounterexample exg2 ghci g2config fc
    case v_cex of
        True -> return . Right $ [Pos fc]
        False -> return . Left $ cex
cexsToFuncConstraints exg2 ghci g2config cex@(CallsCounter _ fc []) = do
    v_cex <- checkCounterexample exg2 ghci g2config fc
    case v_cex of
        True -> return . Right $ [Pos fc]
        False -> return . Left $ cex
