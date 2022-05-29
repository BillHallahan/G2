module G2.Solver.Maximize ( MaximizeSolver
                          , mkMaximizeSolver) where

import G2.Solver.Converters
import G2.Solver.Language
import G2.Solver.Solver

import Control.Concurrent
import Control.Concurrent.MVar
import Data.IORef
import Data.List as L
import qualified Data.Map as M
import Text.Builder

data MaximizeSolver con = MaxSolver (MVar ThreadId) (MVar (Result () () ())) (IORef [SMTHeader]) con

mkMaximizeSolver :: SMTConverter con => con -> IO (MaximizeSolver con)
mkMaximizeSolver con = do
    thread_mvar <- newEmptyMVar
    res_mvar <- newEmptyMVar
    headers_io_ref <- newIORef []
    return $ MaxSolver thread_mvar res_mvar headers_io_ref con

instance SMTConverter con => Solver (MaximizeSolver con) where
    check solver _ pc = checkConstraintsPC solver pc
    solve (MaxSolver _ _ _ con) = solve con
    close = closeIO

instance SMTConverter con => SMTConverter (MaximizeSolver con) where
    closeIO (MaxSolver thread_ioref _ _ con) = do
        maybe (return ()) killThread =<< tryReadMVar thread_ioref
        closeIO con

    reset (MaxSolver thread_mvar res_mvar headers_io_ref con) = do
        maybe (return ()) killThread =<< tryReadMVar thread_mvar
        _ <- tryTakeMVar thread_mvar
        _ <- tryTakeMVar res_mvar
        writeIORef headers_io_ref []
        reset con

    checkSatInstr (MaxSolver thread_mvar res_mvar headers_io_ref con) = do
        maybe (return ()) killThread =<< tryReadMVar thread_mvar
        added <- readIORef headers_io_ref
        thread <- forkIO (do
                            res <- solveSoftAsserts con added
                            definitelyPutMVar res_mvar res)
        definitelyPutMVar thread_mvar thread
        return ()

    maybeCheckSatResult (MaxSolver _ res_ioref _ _) = tryReadMVar res_ioref

    getModelInstrResult (MaxSolver _ _ _ con) = getModelInstrResult con
    getUnsatCoreInstrResult (MaxSolver _ _ _ con) = getUnsatCoreInstrResult con

    setProduceUnsatCores (MaxSolver _ _ _ con) = setProduceUnsatCores con

    addFormula (MaxSolver _ _ headers_io_ref con) form = modifyIORef' headers_io_ref (form ++)

    checkSatGetModelOrUnsatCoreNoReset (MaxSolver _ _ headers_io_ref con) headers vs = do
        added <- readIORef headers_io_ref
        res <- solveSoftAsserts con (added ++ headers)
        case res of
            SAT _ -> do
                mdl <- getModelInstrResult con vs
                return (SAT mdl)
            UNSAT _ -> do
                uc <- getUnsatCoreInstrResult con
                return (UNSAT uc)
            Unknown err _ -> return (Unknown err ())

    -- We don't need to produce a model, because this resets, so we can just ignore all soft assertions
    checkSat max_solver@(MaxSolver _ _ _ con) headers = do
        reset max_solver
        checkSat con $ filter (\h -> case h of AssertSoft _ _ -> False; _ -> True) headers

    checkSatGetModel con@(MaxSolver _ _ _ _) headers vs = do
        reset con
        res <- solveSoftAsserts con headers
        case res of
            SAT _ -> do
                mdl <- getModelInstrResult con vs
                return (SAT mdl)
            UNSAT _ -> return (UNSAT ())
            Unknown err _ -> return (Unknown err ())

    push (MaxSolver _ _ _ con) = push con
    pop (MaxSolver _ _ _ con) = pop con

solveSoftAsserts :: SMTConverter con => con -> [SMTHeader] -> IO (Result () () ())
solveSoftAsserts con headers = do
    let (soft_asserts, other_headers) =
            partition (\h -> case h of AssertSoft _ _ -> True; _ -> False) $ elimSetLogic headers
        set_logic = getSetLogic headers
        soft_assert_sum =
              foldr (:+) (VInt 0)
            $ map (\(AssertSoft assrt _) -> Ite assrt (VInt 1) (VInt 0)) soft_asserts
        new_assert = Assert $ V totalVarName SortInt := soft_assert_sum
        var_decl = VarDecl (string totalVarName) SortInt
    setProduceUnsatCores con
    addHeaders con (set_logic ++ var_decl:other_headers ++ [new_assert])
    solveSoftAsserts' con Nothing 0 0 (genericLength soft_asserts)

type Minimum = Integer
type Maximum = Integer

solveSoftAsserts' :: SMTConverter con =>
                     con
                  -> Maybe SMTModel
                  -> Int
                  -> Minimum
                  -> Maximum
                  -> IO (Result () () ())
solveSoftAsserts' con mb_mdl fresh min_ max_ = do
    let (target_q, target_r) = (min_ + max_) `quotRem` 2
        target = target_q + target_r
        target_assert = Assert $ V totalVarName SortInt :>= VInt target

    putStrLn $ "min = " ++ show min_ ++ ", max = " ++ show max_ ++ ", target = " ++ show target
    push con
    res <- constraintsToModelOrUnsatCoreNoReset con [target_assert] [(totalVarName, SortInt)]
    case res of
        SAT mdl | Just (VInt new_min_) <- m_new_min
                , new_min_ == max_ -> return $ SAT ()
                | Just (VInt new_min_) <- m_new_min -> do
                    -- If we are increasing the minimum depth, we do NOT want to remove
                    -- our previous limit assertion, so that if we later get a model, that
                    -- limit assertion is still in place.
                    solveSoftAsserts' con (Just mdl) (fresh + 1) (new_min_ + 1) max_
                -- Should be unreachable because totalVarName should always be in the model
                | otherwise -> error "solveSoftAsserts': Impossible case"
            where
               m_new_min = M.lookup totalVarName mdl
        UNSAT _ | target == 0 -> return $ UNSAT ()
                | min_ == max_ -> do
                    pop con
                    return $ SAT ()
                -- Should be unreachable, because if min_ is not 0, we have found a model.
                -- But if min_ == max_ == 0, target == 0, and we hit the first case.
                | min_ == max_ -> error "solveSoftAsserts': Impossible case"
                | otherwise -> do
                  pop con
                  solveSoftAsserts' con mb_mdl (fresh + 1) min_ (target - 1)
        Unknown err _ -> return $ Unknown err ()

definitelyPutMVar :: MVar a -> a -> IO ()
definitelyPutMVar mvar a = do
    r <- tryPutMVar mvar a
    case r of
      True -> return ()
      False -> modifyMVar_ mvar (\_ -> return a)

totalVarName :: SMTName
totalVarName = "solveSoftAsserts_SUM_VAR"

getSetLogic :: [SMTHeader] -> [SMTHeader]
getSetLogic = filter (\h -> case h of SetLogic _ -> True; _ -> False)

elimSetLogic :: [SMTHeader] -> [SMTHeader]
elimSetLogic = filter (\h -> case h of SetLogic _ -> False; _ -> True)
