module G2.Solver.Maximize ( MaximizeSolver (..)
                          , solveSoftAsserts) where

import G2.Solver.Converters
import G2.Solver.Language
import G2.Solver.Solver

import Data.List as L
import qualified Data.Map as M
import Text.Builder

data MaximizeSolver con = MaxSolver con

instance SMTConverter con => Solver (MaximizeSolver con) where
    check solver _ pc = checkConstraintsPC solver pc
    solve con = checkModelPC undefined con
    close = closeIO

instance SMTConverter con => SMTConverter (MaximizeSolver con) where
    closeIO (MaxSolver con) = closeIO con

    reset (MaxSolver con) = reset con

    setProduceUnsatCores (MaxSolver con) = setProduceUnsatCores con

    addFormula (MaxSolver con) form = addFormula con form

    checkSatGetModelOrUnsatCoreNoReset (MaxSolver con) headers vs = do
        res <- solveSoftAsserts con headers vs
        case res of
            SAT mdl -> return (SAT mdl)
            UNSAT uc -> return (UNSAT uc)
            Unknown err _ -> return (Unknown err ())

    -- We don't need to produce a model, so we can just ignore all soft assertions
    checkSat (MaxSolver con) headers = checkSat con $ filter (\h -> case h of AssertSoft _ _ -> False; _ -> True) headers

    checkSatGetModel con headers vs = do
        res <- solveSoftAsserts con headers vs
        case res of
            SAT mdl -> return (SAT mdl)
            UNSAT _ -> return (UNSAT ())
            Unknown err _ -> return (Unknown err ())

    push (MaxSolver con) = push con
    pop (MaxSolver con) = pop con

solveSoftAsserts :: SMTConverter con => con -> [SMTHeader] -> [(SMTName, Sort)] -> IO (Result SMTModel UnsatCore (Maybe SMTModel))
solveSoftAsserts con headers vs = do
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
    solveSoftAsserts' con vs Nothing 0 0 (genericLength soft_asserts)

type Minimum = Integer
type Maximum = Integer

solveSoftAsserts' :: SMTConverter con =>
                     con
                  -> [(SMTName, Sort)]
                  -> Maybe SMTModel
                  -> Int
                  -> Minimum
                  -> Maximum
                  -> IO (Result SMTModel UnsatCore (Maybe SMTModel))
solveSoftAsserts' con vs mb_mdl fresh min_ max_ = do
    let (target_q, target_r) = (min_ + max_) `quotRem` 2
        target = target_q + target_r
        target_assert = Assert $ V totalVarName SortInt :>= VInt target

    putStrLn $ "min = " ++ show min_ ++ ", max = " ++ show max_ ++ ", target = " ++ show target
    push con
    res <- constraintsToModelOrUnsatCoreNoReset con [target_assert] ((totalVarName, SortInt):vs)
    pop con
    case res of
        SAT mdl | Just (VInt new_min_) <- m_new_min
                , new_min_ == max_ -> return $ SAT mdl
                | Just (VInt new_min_) <- m_new_min -> solveSoftAsserts' con vs (Just mdl) (fresh + 1) (new_min_ + 1) max_
                -- Should be unreachable because totalVarName should always be in the model
                | otherwise -> error "solveSoftAsserts': Impossible case"
            where
               m_new_min = M.lookup totalVarName mdl
        UNSAT uc | target == 0 -> return $ UNSAT uc
                 | min_ == max_, Just mdl <- mb_mdl -> return $ SAT mdl
                 -- Should be unreachable, because if min_ is not 0, we have found a model.
                 -- But if min_ == max_ == 0, target == 0, and we hit the first case.
                 | min_ == max_ -> error "solveSoftAsserts': Impossible case"
                 | otherwise -> solveSoftAsserts' con vs mb_mdl (fresh + 1) min_ (target - 1)
        Unknown err _ -> return $ Unknown err mb_mdl

totalVarName :: SMTName
totalVarName = "solveSoftAsserts_SUM_VAR"

getSetLogic :: [SMTHeader] -> [SMTHeader]
getSetLogic = filter (\h -> case h of SetLogic _ -> True; _ -> False)

elimSetLogic :: [SMTHeader] -> [SMTHeader]
elimSetLogic = filter (\h -> case h of SetLogic _ -> False; _ -> True)
