{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module MergeStateUnitTests ( mergeCurrExprTests
                 , checkRelAssumeTests
                 , solveRelAssumeTests) where

import G2.Interface
import G2.Language as G2
import G2.Translation
import G2.Execution.StateMerging as SM
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.ExprEnv as EE
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as Stack
import qualified G2.Language.TypeClasses.TypeClasses as TC
import G2.Solver

import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.HashSet as S
import qualified Data.HashMap.Lazy as HM
import System.FilePath

type TestNum = Int

mergeCurrExprTests :: Either String Bool
mergeCurrExprTests = if not (null errs)
            then Left (foldr concatErrMsgs "" errs)
            else Right True
        where
            errs = filter selectErrors $ zipWith (compareWithErrMsg "Error merging CurrExprs. Expected: ")
                [(1, expectedVal1), (2, expectedVal2), (3, expectedVal3), (4, expectedVal4), (5, expectedVal5), (6, expectedVal6)]
-- import G2.Execution.StateMerging as SM
                [g2Val1, g2Val2, g2Val3, g2Val4, g2Val5, g2Val6]

checkRelAssumeTests :: IO (Either String Bool)
checkRelAssumeTests = do
        let kv = simpleKV
            statePCs = createStatePCs kv --list of PathConds from which to create new states
            checkPCs = createTestPCs kv -- list of NewPCs to check with the corresponding state
            expected = checkRelAssumeExpected -- list of (test number, expected result) tuples
            assPCSol = AssumePCSolver (Tr {unTr = ADTSolver})
            states = createTestStates kv statePCs
        
        results <- sequence $ zipWith (\s pc -> do (r, _) <- checkTr assPCSol s pc
                                                   return r) states checkPCs
            
        let errs = filter selectErrors $ zipWith (compareWithErrMsg "Error in AssumePCSolver.") expected results
        if not (null errs)
           then return $ Left (foldr concatErrMsgs " " errs)
           else return $ Right True

solveRelAssumeTests :: IO (Either String Bool)
solveRelAssumeTests = do
        let kv = simpleKV
            b = createTestBindings
            statePCs = createStatePCs kv --list of PathConds from which to create new states
            checkPCs = createTestPCs kv -- list of NewPCs to check with the corresponding state
            is = createTestIds -- list of list of Ids for each test
            expected = solveRelAssumeExpected -- list of (test number, expected result) tuples
            assPCSol = AssumePCSolver (Tr {unTr = ADTSolver})
            states = createTestStates kv statePCs
        
        results <- sequence $ zipWith3 (\s i pc -> do (r, m, _) <- solveTr assPCSol s b i pc
                                                      return (r, m)) states is checkPCs
            
        let errs = filter selectErrors $ zipWith (compareWithErrMsg "Error in AssumePCSolver. ") expected results
        if not (null errs)
           then return $ Left (foldr concatErrMsgs " " errs)
           else return $ Right True

selectErrors :: Either String Bool -> Bool
selectErrors (Left _) = True
selectErrors (Right _) = False

concatErrMsgs :: Either String Bool -> String -> String
concatErrMsgs (Left e') e = e ++ "\n" ++ e'
concatErrMsgs (Right _) _ = "Error. No error message to concatenate"

compareWithErrMsg :: Eq a => Show a => String -> (TestNum, a) -> a -> Either String Bool
compareWithErrMsg errMsg (i, expected) actual =  if expected == actual
    then Right True
    else Left (errMsg ++ " Test number " ++ (show i) ++ " - Expected: " ++ (show expected) ++ "\n Got: " ++ (show actual))

-- Following functions return individual test outputs or expected output values

-- mergeCurrExpr Tests
g2Val1 :: CurrExpr -- simple test
g2Val1 = SM.mergeCurrExpr kv idX (CurrExpr Evaluate (App e1 e2)) (CurrExpr Evaluate (App e1 e2'))
    where
        kv = simpleKV

g2Val2 :: CurrExpr
g2Val2 = SM.mergeCurrExpr kv idX
    (CurrExpr Evaluate (App e1 (App e2 e3)))
    (CurrExpr Evaluate (App e1 (App e2' e3')))
    where
        kv = simpleKV

g2Val3 :: CurrExpr -- force NonDet further down
g2Val3 = SM.mergeCurrExpr kv idX 
    (CurrExpr Evaluate (App e1 (App e2 e3))) 
    (CurrExpr Evaluate (App e1 (App e2 e3')))
    where
        kv = simpleKV

g2Val4 :: CurrExpr -- identical expressions
g2Val4 = SM.mergeCurrExpr kv idX
    (CurrExpr Evaluate (App e1 (App e2 e3)))
    (CurrExpr Evaluate (App e1 (App e2 e3)))
    where
        kv = simpleKV
-- import G2.Execution.StateMerging as SM

g2Val5 :: CurrExpr -- identical expressions 2
g2Val5 = SM.mergeCurrExpr kv idX
    (CurrExpr Evaluate (App e1 (App e4 e3)))
    (CurrExpr Evaluate (App e1 (App e4 e3')))
    where
        kv = simpleKV

g2Val6 :: CurrExpr -- Nested (App ...) in first argument
g2Val6 = SM.mergeCurrExpr kv idX
    (CurrExpr Evaluate (App (App e1 e2) (App e4 e3)))
    (CurrExpr Evaluate (App (App e1 e2') (App e4 e3')))
    where
        kv = simpleKV

expectedVal1 :: CurrExpr
expectedVal1 = CurrExpr Evaluate
    (App e1
        (NonDet [(Assume Nothing xEq1 e2), (Assume Nothing xEq2 e2')])
    )

expectedVal2 :: CurrExpr
expectedVal2 = CurrExpr Evaluate
    (App e1
        (App
            (NonDet [(Assume Nothing xEq1 e2), (Assume Nothing xEq2 e2')])
            (NonDet [(Assume Nothing xEq1 e3), (Assume Nothing xEq2 e3')])
        )
    )

expectedVal3 :: CurrExpr
expectedVal3 = CurrExpr Evaluate
    (App e1
        (App e2
            (NonDet [(Assume Nothing xEq1 e3), (Assume Nothing xEq2 e3')])
        )
    )

expectedVal4 :: CurrExpr
expectedVal4 = CurrExpr Evaluate (App e1 (App e2 e3))

expectedVal5 :: CurrExpr
expectedVal5 = CurrExpr Evaluate
    (App e1
        (App e4
            (NonDet [(Assume Nothing xEq1 e3), (Assume Nothing xEq2 e3')])
        )
    )

expectedVal6 :: CurrExpr
expectedVal6 = CurrExpr Evaluate
    (App
        (App e1
            (NonDet [(Assume Nothing xEq1 e2), (Assume Nothing xEq2 e2')])
        )
        (App e4
            (NonDet [(Assume Nothing xEq1 e3), (Assume Nothing xEq2 e3')])
        )
    )

e1 :: Expr
e1 = (Data (DataCon (Name "$I" Nothing 0 Nothing) TYPE))

e2 :: Expr
e2 = (Lit (LitInt 2))

e2' :: Expr
e2' = (Lit (LitInt 4))

e3 :: Expr
e3 = (Lit (LitInt 6))

e3' :: Expr
e3' = (Lit (LitInt 8))

e4 :: Expr
e4 = (Data (DataCon (Name "$J" Nothing 0 Nothing) TYPE))

idX :: Id
idX = (Id (Name "X" Nothing 0 Nothing) TyLitInt)

varX :: Expr
varX = (Var idX)

eqTo :: Expr
eqTo = (Prim Eq (TyFun TyLitInt (TyFun TyLitInt (TyCon (Name "Bool" Nothing 0 Nothing) TYPE))))

xEq1 :: Expr
xEq1 = (App (App eqTo varX) (Lit (LitInt 1)))

xEq2 :: Expr
xEq2 = (App (App eqTo varX) (Lit (LitInt 2)))

-- checkRelAssume Tests
createStatePCs :: KV.KnownValues -> [PathConds]
createStatePCs kv = take 9 (repeat (PC.fromList kv []))

ty1N :: Name
ty1N = (Name "Ty1" Nothing 20 Nothing) 

ty1T :: Type
ty1T = (TyCon ty1N TYPE)

dconA :: DataCon
dconA = (DataCon (Name "A" Nothing 17 Nothing) ty1T)

dconB :: DataCon
dconB = (DataCon (Name "B" Nothing 18 Nothing) ty1T)

ty1 :: AlgDataTy
ty1 = DataTyCon {bound_ids = [], data_cons = [dconA, dconB]}

ty2N :: Name
ty2N = (Name "Ty2" Nothing 23 Nothing)

ty2T :: Type
ty2T = (TyCon ty2N TYPE)

dconC :: DataCon
dconC = (DataCon (Name "C" Nothing 24 Nothing) ty2T)

dconD :: DataCon
dconD = (DataCon (Name "D" Nothing 25 Nothing) ty2T)

ty2 :: AlgDataTy
ty2 = DataTyCon {bound_ids = [], data_cons = [dconC, dconD]}

var1N :: Name
var1N = (Name "1" Nothing 19 Nothing)

var1 :: Expr
var1 = Var (Id var1N ty1T)

var2N :: Name
var2N = (Name "2" Nothing 26 Nothing)

var2 :: Expr
var2 = Var (Id var2N ty2T)

createTestPCs :: KV.KnownValues -> [PathConds]
createTestPCs kv = [ PC.fromList kv [ -- simple test
                        AssumePC idX 1 
                        (ConsCond dconA var1 True)]
                   , PC.fromList kv [
                        AssumePC idX 1 
                        (ConsCond dconA var1 False)
                        , AssumePC idX 1 
                        (ConsCond dconB var1 False)]
                   , PC.fromList kv [ -- combination of AssumePCs and other PathCond-s
                        ConsCond dconA var1 False
                        , (ConsCond dconB var1 False)
                        , AssumePC idX 1 
                        (ConsCond dconA var1 False)]
                   , PC.fromList kv [ -- Set of (AssumePCs id i pc) with i == 2 should be satisfiable, hence entire PathConds should be satisfiable
                        AssumePC idX 1 
                        (ConsCond dconA var1 False)
                        , AssumePC idX 1 
                        (ConsCond dconB var1 False)
                        , AssumePC idX 2 
                        (ConsCond dconA var1 True)
                        , AssumePC idX 2 
                        (ConsCond dconB var1 False)]
                   , PC.fromList kv [ 
                        AssumePC idX 1 
                        (ConsCond dconA var1 False)
                        , AssumePC idX 1 
                        (ConsCond dconB var1 False)
                        , AssumePC (Id (Name "Y" Nothing 0 Nothing) TyLitInt) 1 
                        (ConsCond dconA var1 True)]
                   , PC.fromList kv [ -- simple nested AssumePCs 
                        AssumePC idX 1 
                        (AssumePC (Id (Name "Y" Nothing 22 Nothing) TyLitInt) 1
                            (ConsCond dconA var1 True))
                        , AssumePC idX 1 
                        (AssumePC (Id (Name "Y" Nothing 22 Nothing) TyLitInt) 1
                            (ConsCond dconB var1 False))]
                   , PC.fromList kv [ -- simple nested AssumePCs (negative test)
                        AssumePC idX 1 
                        (AssumePC (Id (Name "Y" Nothing 22 Nothing) TyLitInt) 1
                            (ConsCond dconA var1 False))
                        , AssumePC idX 1 
                        (AssumePC (Id (Name "Y" Nothing 22 Nothing) TyLitInt) 1
                            (ConsCond dconB var1 False))]
                   , PC.fromList kv [ -- Multiple solutions possible
                        AssumePC idX 1 
                        (ConsCond dconB var1 True)
                        , AssumePC idX 2 
                        (ConsCond dconA var1 True)]
                   , PC.fromList kv [ -- Multiple Data types
                        AssumePC idX 1 
                        (ConsCond dconB var1 True)
                        , AssumePC idX 1 
                        (ConsCond dconD var2 True)
                        , AssumePC idX 2 
                        (ConsCond dconA var1 False)
                        , AssumePC idX 2 
                        (ConsCond dconA var1 True)]
                   ]

checkRelAssumeExpected :: [(TestNum, Result)]
checkRelAssumeExpected = [(1, SAT), (2, UNSAT), (3, UNSAT), (4, SAT), (5, UNSAT), (6, SAT), (7, UNSAT), (8, SAT), (9, SAT)]

-- solveRelAssumeTests
createTestIds :: [[Id]]
createTestIds = [[Id var1N ty1T]
                , [Id var1N ty1T]
                , [Id var1N ty1T]
                , [Id var1N ty1T]
                , [Id var1N ty1T]
                , [Id var1N ty1T]
                , [Id var1N ty1T]
                , [Id var1N ty1T]
                , [Id var1N ty1T, Id var2N ty2T]
                ]

solveRelAssumeExpected :: [(TestNum, (Result, Maybe Model))]
solveRelAssumeExpected = [ (1, (SAT, Just (M.fromList [(var1N, Data dconA)])))
                         , (2, (UNSAT, Nothing))
                         , (3, (UNSAT, Nothing))
                         , (4, (SAT, Just (M.fromList [(var1N, Data dconA)])))
                         , (5, (UNSAT, Nothing))
                         , (6, (SAT, Just (M.fromList [(var1N, Data dconA)])))
                         , (7, (UNSAT, Nothing))
                         , (8, (SAT, Just (M.fromList [(var1N, Data dconB)])))
                         , (9, (SAT, Just (M.fromList [(var1N, Data dconB)
                            , (var2N, Data dconD)])))
                         ]

-- Helper Functions
simpleKV :: KV.KnownValues
simpleKV = KV.KnownValues
            { KV.tyInt = (Name "" Nothing 0 Nothing)
            , KV.dcInt = (Name "" Nothing 0 Nothing)
 
            , KV.tyFloat = (Name "" Nothing 0 Nothing)
            , KV.dcFloat = (Name "" Nothing 0 Nothing)

            , KV.tyDouble = (Name "" Nothing 0 Nothing)
            , KV.dcDouble = (Name "" Nothing 0 Nothing)

            , KV.tyInteger = (Name "" Nothing 0 Nothing)
            , KV.dcInteger = (Name "" Nothing 0 Nothing)

            , KV.tyBool = (Name "Bool" Nothing 0 Nothing)
            , KV.dcTrue = (Name "" Nothing 0 Nothing)
            , KV.dcFalse = (Name "" Nothing 0 Nothing)

            , KV.tyList = (Name "" Nothing 0 Nothing)
            , KV.dcCons = (Name "" Nothing 0 Nothing)
            , KV.dcEmpty = (Name "" Nothing 0 Nothing)

            , KV.eqTC = (Name "" Nothing 0 Nothing)
            , KV.numTC = (Name "" Nothing 0 Nothing)
            , KV.ordTC = (Name "" Nothing 0 Nothing)
            , KV.integralTC = (Name "" Nothing 0 Nothing)

            , KV.eqFunc = (Name "" Nothing 0 Nothing)
            , KV.neqFunc = (Name "" Nothing 0 Nothing)

            , KV.plusFunc = (Name "" Nothing 0 Nothing)
            , KV.minusFunc = (Name "" Nothing 0 Nothing)
            , KV.timesFunc = (Name "" Nothing 0 Nothing)
            , KV.divFunc = (Name "" Nothing 0 Nothing)
            , KV.negateFunc = (Name "" Nothing 0 Nothing)
            , KV.modFunc = (Name "" Nothing 0 Nothing)

            , KV.fromIntegerFunc = (Name "" Nothing 0 Nothing)
            , KV.toIntegerFunc = (Name "" Nothing 0 Nothing)

            , KV.geFunc = (Name "" Nothing 0 Nothing)
            , KV.gtFunc = (Name "" Nothing 0 Nothing)
            , KV.ltFunc = (Name "" Nothing 0 Nothing)
            , KV.leFunc = (Name "" Nothing 0 Nothing)
            , KV.structEqTC = (Name "" Nothing 0 Nothing)
            , KV.structEqFunc = (Name "" Nothing 0 Nothing)
  
            , KV.andFunc = (Name "" Nothing 0 Nothing)
            , KV.orFunc = (Name "" Nothing 0 Nothing)
            , KV.patErrorFunc = (Name "" Nothing 0 Nothing)
            }

createInitState :: FilePath
                   -> String
                   -> Config
                   -> IO (State ())
createInitState src entry config = do
    let proj = takeDirectory src
    (mb_modname, exg2) <- translateLoaded proj src [] simplTranslationConfig config

    let (init_state, _ , _) = initState exg2 Nothing Nothing False (T.pack entry) mb_modname config
    return (init_state)

createTestState :: KnownValues -> TypeEnv -> PathConds -> State ()
createTestState kv tenv pc = State {
      expr_env = EE.empty
    , type_env = tenv
    , curr_expr = CurrExpr Evaluate (Lit (LitInt 0))
    , path_conds = pc
    , non_red_path_conds = []
    , true_assert = True
    , assert_ids = Nothing
    , type_classes = TC.initTypeClasses []
    , symbolic_ids = []
    , exec_stack = Stack.empty
    , model = M.empty
    , known_values = kv
    , rules = []
    , num_steps = 0
    , track = ()
    , tags = S.empty
    }

createTestStates :: KnownValues -> [PathConds] -> [State ()]
createTestStates kv pcs = map (createTestState kv (M.fromList [(ty1N, ty1), (ty2N, ty2)])) pcs

createTestBindings :: Bindings
createTestBindings = Bindings {
    deepseq_walkers = M.empty
    , fixed_inputs = []
    , arb_value_gen = arbValueInit
    , cleaned_names = HM.empty
    , input_names = []
    , higher_order_inst = []
    , rewrite_rules = []
    , name_gen = mkNameGen [ty1N, ty2N, (Name "A" Nothing 17 Nothing), (Name "B" Nothing 18 Nothing), (Name "X" Nothing 0 Nothing), (Name "Y" Nothing 22 Nothing)
        , (Name "Bool" Nothing 0 Nothing), (Name "" Nothing 0 Nothing), (Name "C" Nothing 24 Nothing), (Name "B" Nothing 25 Nothing)]
    }

