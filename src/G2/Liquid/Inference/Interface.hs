module G2.Liquid.Inference.Interface (inference) where

import G2.Config.Config as G2
import G2.Execution.Memory
import G2.Interface
import qualified G2.Language.ExprEnv as E
import G2.Language.Naming
import G2.Language.Support
import G2.Language.Syntax
import G2.Liquid.Inference.FuncConstraint
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.PolyRef
import G2.Liquid.Helpers
import G2.Liquid.Inference.RefSynth
import G2.Liquid.Inference.GeneratedSpecs
import G2.Liquid.Inference.Verify
import G2.Liquid.Interface
import G2.Liquid.Types
import G2.Translation

import Language.Haskell.Liquid.Types as LH

import Control.Monad
import Data.Either
import Data.List
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
    let simp_s = initSimpleState (snd exg2)
        lrs = createStateForInference simp_s g2config ghci

    inference' g2config lhconfig' ghci (fst exg2) lrs emptyGS emptyFC 

inference' :: G2.Config -> LH.Config -> [GhcInfo] -> Maybe T.Text -> LiquidReadyState
           -> GeneratedSpecs -> FuncConstraints -> IO (Either [CounterExample] GeneratedSpecs)
inference' g2config lhconfig ghci m_modname lrs gs fc = do
    print gs

    let merged_ghci = addSpecsToGhcInfos ghci gs
    mapM_ (print . gsTySigs . spec) merged_ghci

    res <- verify lhconfig merged_ghci

    case res of
        Safe -> return $ Right gs
        Crash -> error "Crash"
        Unsafe bad -> do
            -- Generate constraints
            let bad' = nub $ map nameOcc bad

            putStrLn $ "bad' = " ++ show bad'

            res <- mapM (genNewConstraints merged_ghci m_modname lrs g2config) bad'

            putStrLn "Before checkNewConstraints"
            new_fc <- checkNewConstraints ghci lrs g2config (concat res)
            putStrLn "After checkNewConstraints"
            case new_fc of
                Left ce -> return . Left $ ce
                Right new_fc' -> do
                    let new_fc_funcs = nub $ map (funcName . constraint) new_fc'

                        fc' = foldr insertFC fc new_fc'

                    -- Synthesize
                    putStrLn "Before genMeasureExs"
                    meas_ex <- genMeasureExs lrs merged_ghci g2config fc'
                    putStrLn "After genMeasureExs"
                    gs' <- foldM (synthesize ghci lrs meas_ex fc') gs new_fc_funcs
                    
                    inference' g2config lhconfig ghci m_modname lrs gs' fc'

createStateForInference :: SimpleState -> G2.Config -> [GhcInfo] -> LiquidReadyState
createStateForInference simp_s config ghci =
    let
        (s, b) = initStateFromSimpleState simp_s True 
                    (\_ ng _ _ _ _ -> (Prim Undefined TyBottom, [], [], ng))
                    (\_ -> [])
                    config
    in
    createLiquidReadyState s b ghci


genNewConstraints :: [GhcInfo] -> Maybe T.Text -> LiquidReadyState -> G2.Config -> T.Text -> IO [CounterExample]
genNewConstraints ghci m lrs g2config n = do
    ((exec_res, _), i) <- runLHInferenceCore n m lrs ghci g2config
    return $ map (lhStateToCE i) exec_res

checkNewConstraints :: [GhcInfo] -> LiquidReadyState -> G2.Config -> [CounterExample] -> IO (Either [CounterExample] [FuncConstraint])
checkNewConstraints ghci lrs g2config cexs = do
    res <- mapM (cexsToFuncConstraints lrs ghci g2config) cexs
    case lefts res of
        res'@(_:_) -> return . Left $ res'
        _ -> return . Right . concat . rights $ res

genMeasureExs :: LiquidReadyState -> [GhcInfo] -> G2.Config -> FuncConstraints -> IO MeasureExs
genMeasureExs lrs ghci g2config fcs =
    let
        es = concatMap (\fc ->
                    let
                        cons = constraint fc
                        ex_poly = concat $ concatMap extractValues $ extractExprPolyBound (returns cons)
                    in
                    returns cons:arguments cons ++ ex_poly
                ) (allFC fcs)
    in
    evalMeasures lrs ghci g2config es

synthesize :: [GhcInfo] -> LiquidReadyState -> MeasureExs -> FuncConstraints -> GeneratedSpecs -> Name -> IO GeneratedSpecs
synthesize ghci lrs meas_ex fc gs n = do
    let eenv = expr_env . state $ lr_state lrs
        tc = type_classes . state $ lr_state lrs

        fc_of_n = lookupFC n fc
        spec = case findFuncSpec ghci n of
                Just spec' -> spec'
                Nothing -> error $ "synthesize: No spec found for " ++ show n
        e = case E.occLookup (nameOcc n) (nameModule n) eenv of
                Just e' -> e'
                Nothing -> error $ "synthesize: No expr found"

        meas = lrsMeasures ghci lrs

    new_spec <- refSynth spec e tc meas meas_ex fc_of_n (measureSymbols ghci)

    putStrLn $ "spec = " ++ show spec
    putStrLn $ "new_spec = " ++ show new_spec

    return $ insertGS n new_spec gs

cexsToFuncConstraints :: LiquidReadyState -> [GhcInfo] -> G2.Config -> CounterExample -> IO (Either CounterExample [FuncConstraint])
cexsToFuncConstraints _ _ _ (DirectCounter _ fcs@(_:_)) =
    return . Right $ map (Pos . real) fcs ++ map (Neg . abstract) fcs
cexsToFuncConstraints _ _ _ (CallsCounter _ _ fcs@(_:_)) =
    return . Right $ map (Pos . real) fcs ++ map (Neg . abstract) fcs
cexsToFuncConstraints lrs ghci g2config cex@(DirectCounter fc []) = do
    v_cex <- checkCounterexample lrs ghci g2config fc
    case v_cex of
        True -> return . Right $ [Pos fc]
        False -> return . Left $ cex
cexsToFuncConstraints lrs ghci g2config cex@(CallsCounter _ fc []) = do
    v_cex <- checkCounterexample lrs ghci g2config fc
    case v_cex of
        True -> return . Right $ [Pos fc]
        False -> return . Left $ cex
