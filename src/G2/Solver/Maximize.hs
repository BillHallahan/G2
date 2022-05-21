module G2.Solver.Maximize (solveSoftAsserts) where

import G2.Solver.Converters
import G2.Solver.Language

import Control.Exception
import Data.Coerce
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.List as L
import qualified Data.Map as M
import Text.Builder

solveSoftAsserts :: SMTConverter con ast out io => con -> [SMTHeader] -> [(SMTName, Sort)] -> IO (Result SMTModel UnsatCore (Maybe SMTModel))
solveSoftAsserts con headers vs = do
    let (soft_asserts, other_headers) =
            partition (\h -> case h of AssertSoft _ _ -> True; _ -> False) $ elimSetLogic headers
        set_logic = getSetLogic headers
        soft_assert_sum =
              foldr (:+) (VInt 0)
            $ map (\(AssertSoft assrt _) -> Ite assrt (VInt 1) (VInt 0)) soft_asserts
        new_assert = Assert $ V totalVarName SortInt := soft_assert_sum
        var_decl = VarDecl (string totalVarName) SortInt
    solveSoftAsserts' con (set_logic ++ var_decl:other_headers) new_assert vs Nothing 0 0 (genericLength soft_asserts)

type Minimum = Integer
type Maximum = Integer

solveSoftAsserts' :: SMTConverter con ast out io =>
                     con
                  -> [SMTHeader]
                  -> SMTHeader
                  -> [(SMTName, Sort)]
                  -> Maybe SMTModel
                  -> Int
                  -> Minimum
                  -> Maximum
                  -> IO (Result SMTModel UnsatCore (Maybe SMTModel))
solveSoftAsserts' con headers soft_header vs mb_mdl fresh min_ max_ = do
    let (target_q, target_r) = (min_ + max_) `quotRem` 2
        target = target_q + target_r
        target_assert = Assert $ V totalVarName SortInt :>= VInt target

        pre = "FRESH_NAME_" ++ show fresh ++ "_"
        headers' = renameAllNamedASTs pre $ headers ++ [soft_header, target_assert]

    putStrLn $ "min = " ++ show min_ ++ ", max = " ++ show max_ ++ ", target = " ++ show target
    res <- constraintsToModelOrUnsatCore con headers' ((totalVarName, SortInt):vs)
    case res of
        SAT mdl | Just (VInt new_min_) <- m_new_min
                , new_min_ == max_ -> return $ SAT mdl
                | Just (VInt new_min_) <- m_new_min -> solveSoftAsserts' con headers soft_header vs (Just mdl) (fresh + 1) (new_min_ + 1) max_
                -- Should be unreachable because totalVarName should always be in the model
                | otherwise -> error "solveSoftAsserts': Impossible case"
            where
               m_new_min = M.lookup totalVarName mdl
        UNSAT uc | target == 0 -> return . UNSAT $ HS.map (drop (L.length pre)) uc
                 | min_ == target - 1, Just mdl <- mb_mdl -> return $ SAT mdl
                 -- Should be unreachable, because if min_ is not 0, we have found a model.
                 -- But if min_ == max_ == 0, target == 0, and we hit the first case.
                 | min_ == max_ -> error "solveSoftAsserts': Impossible case"
                 | otherwise -> solveSoftAsserts' con headers soft_header vs mb_mdl (fresh + 1) min_ (target - 1)
        Unknown err _ -> return $ Unknown err mb_mdl

totalVarName :: SMTName
totalVarName = "solveSoftAsserts_SUM_VAR"

getSetLogic :: [SMTHeader] -> [SMTHeader]
getSetLogic = filter (\h -> case h of SetLogic _ -> True; _ -> False)

elimSetLogic :: [SMTHeader] -> [SMTHeader]
elimSetLogic = filter (\h -> case h of SetLogic _ -> False; _ -> True)

formulaNames :: [SMTHeader] -> [SMTName]
formulaNames = evalASTs go
    where
        go (Named _ nm) = [nm]
        go _ = []

renameNamedASTs :: HM.HashMap SMTName SMTName -> [SMTHeader] -> [SMTHeader]
renameNamedASTs m = modifyASTs go
    where
        go (Named smt nm) | Just new_nm <- HM.lookup nm m = Named smt new_nm
        go smt = smt

renameAllNamedASTs :: String -> [SMTHeader] -> [SMTHeader]
renameAllNamedASTs fresh headers =
    let
        ns = formulaNames headers
        m = HM.fromList $ map (\n -> (n, fresh ++ n)) ns
    in
    renameNamedASTs m headers
