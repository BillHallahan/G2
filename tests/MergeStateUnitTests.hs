{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module MergeStateUnitTests (
                 mergeCurrExprTests
                 , checkADTNumericalTests
                 , solveADTNumericalTests) where

import G2.Interface
import G2.Language as G2
import G2.Translation
import G2.Initialization.MkCurrExpr
import G2.Execution.StateMerging as SM
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.ExprEnv as EE
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as Stack
import qualified G2.Language.TypeClasses.TypeClasses as TC
import G2.Solver
import G2.Config

import Data.Maybe
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Set as S
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import System.FilePath

type TestNum = Int

mergeCurrExprTests :: Either String Bool
mergeCurrExprTests = if not (null errs)
            then Left (foldr concatErrMsgs "" errs)
            else Right True
        where
            errs = filter selectErrors $ zipWith (compareWithErrMsg "Error merging CurrExprs. ")
                [(1, (== expectedVal1)), (2, (== expectedVal2)), (3, (== expectedVal3)), (4, (== expectedVal4))
                , (5,(== expectedVal5)), (6, check6), (7, check7)]
                [g2Val1, g2Val2, g2Val3, g2Val4, g2Val5, g2Val6]

checkADTNumericalTests :: IO (Either String Bool)
checkADTNumericalTests = do
    let kv = simpleKV
        numTests = 10
        statePCs = createStatePCs numTests --list of PathConds from which to create new states
        checkPCs = createTestPCs kv -- list of NewPCs to check with the corresponding state
        expected = checkADTNumExpected -- list of (test number, expected result) tuples
        states = createTestStates kv statePCs

    let avf = arbValue
    SomeSMTSolver con <- getSMTAV avf (createConfig {smt = ConZ3})
    let adtNumSol = GroupRelated avf (ADTNumericalSolver avf con)

    results <- sequence $ zipWith (\s pc -> check adtNumSol s pc) states checkPCs
        
    let errs = filter selectErrors $ zipWith (compareWithErrMsg "Error in Solving.") expected results
    if not (null errs)
       then return $ Left (foldr concatErrMsgs " " errs)
       else return $ Right True

solveADTNumericalTests :: IO (Either String Bool)
solveADTNumericalTests = do
    let kv = simpleKV
        b = createTestBindings
        numTests = 10
        statePCs = createStatePCs numTests --list of PathConds from which to create new states
        checkPCs = createTestPCs kv -- list of NewPCs to check with the corresponding state
        is = createTestIds -- list of list of Ids for each test
        expected = solveADTNumExpected -- list of (test number, expected result) tuples
        states = createTestStates kv statePCs

    let avf = arbValue
    SomeSMTSolver con <- getSMTAV avf (createConfig {smt = ConZ3})
    let adtNumSol = GroupRelated avf (ADTNumericalSolver avf con)

    results <- sequence $ zipWith3 (\s i pc -> solve adtNumSol s b i pc) states is checkPCs

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

compareWithErrMsg :: Show a => String -> (TestNum, (a -> Bool)) -> a -> Either String Bool
compareWithErrMsg errMsg (i, f) actual =  if f actual
    then Right True
    else Left (errMsg ++ " Test number " ++ (show i) ++ " Got: " ++ (show actual))

-- Following functions return individual test outputs or expected output values

-- mergeCurrExpr Tests

--simple test
g2Val1 :: CurrExpr
g2Val1 = snd $ SM.mergeCurrExpr ctxt
    where
        ce1 = (CurrExpr Evaluate (App e1 e2))
        ce2 = (CurrExpr Evaluate (App e1 e2'))
        ctxt = createContext ce1 ce2 Nothing Nothing

-- force NonDet further down
g2Val2 :: CurrExpr
g2Val2 = snd $ SM.mergeCurrExpr ctxt
    where
        ctxt = createContext ce1 ce2 Nothing Nothing
        ce1 = (CurrExpr Evaluate (App e1 (App e2 e3)))
        ce2 = (CurrExpr Evaluate (App e1 (App e2 e3')))

-- Identical
g2Val3 :: CurrExpr
g2Val3 = snd $ SM.mergeCurrExpr ctxt
    where
        ctxt = createContext ce1 ce2 Nothing Nothing
        ce1 = (CurrExpr Evaluate (App e1 (App e2 e3)))
        ce2 = (CurrExpr Evaluate (App e1 (App e2 e3)))

-- Identical expressions 2
g2Val4 :: CurrExpr
g2Val4 = snd $ SM.mergeCurrExpr ctxt
    where
        ctxt = createContext ce1 ce2 Nothing Nothing
        ce1 = (CurrExpr Evaluate (App e1 (App e4 e3)))
        ce2 = (CurrExpr Evaluate (App e1 (App e4 e3')))

-- Nested (App...) in first argument
g2Val5 :: CurrExpr
g2Val5 = snd $ SM.mergeCurrExpr ctxt
    where
        ctxt = createContext ce1 ce2 Nothing Nothing
        ce1 = (CurrExpr Evaluate (App (App e1 e2) (App e4 e3)))
        ce2 = (CurrExpr Evaluate (App (App e1 e2') (App e4 e3')))

-- merge inner case expr in SMNF
g2Val6 :: CurrExpr
g2Val6 = snd $ SM.mergeCurrExpr ctxt
    where
        ctxt = createContext ce1 ce2 Nothing Nothing
        ce1 = (CurrExpr Evaluate
                (App (App e1 e2)
                     (Case varfs1 idfs1 [Alt (LitAlt (LitInt 1)) e2', Alt (LitAlt (LitInt 2)) e3'])
                )
              )
        ce2 = (CurrExpr Evaluate
                (App (App e1 e2')
                     (Case varfs2 idfs2 [Alt (LitAlt (LitInt 1)) e3, Alt (LitAlt (LitInt 2)) e4])
                )
              )

-- merge inner case expr in SMNF, where some choices have common data cons
g2Val7 :: CurrExpr
g2Val7 = snd $ SM.mergeCurrExpr ctxt
    where
        ctxt = createContext ce1 ce2 Nothing Nothing
        ce1 = (CurrExpr Evaluate
                (App (App e1 e2)
                     (Case varfs1 idfs1 [Alt (LitAlt (LitInt 1)) (App e1 e2'), Alt (LitAlt (LitInt 2)) e3'])
                )
              )
        ce2 = (CurrExpr Evaluate
                (App (App e1 e2')
                     (Case varfs2 idfs2 [Alt (LitAlt (LitInt 1)) (App e1 e3), Alt (LitAlt (LitInt 2)) e4])
                )
              )

expectedVal1 :: CurrExpr
expectedVal1 = CurrExpr Evaluate
    (App e1
        (Case (varX) idX [Alt (LitAlt (LitInt 1)) e2, Alt (LitAlt (LitInt 2)) e2'])
    )

expectedVal2 :: CurrExpr
expectedVal2 = CurrExpr Evaluate
    (App e1
        (App e2
            (Case (varX) idX
                [ Alt (LitAlt (LitInt 1)) e3
                , Alt (LitAlt (LitInt 2)) e3'])
        )
    )

expectedVal3 :: CurrExpr
expectedVal3 = CurrExpr Evaluate (App e1 (App e2 e3))

expectedVal4 :: CurrExpr
expectedVal4 = CurrExpr Evaluate
    (App e1
        (App e4
            (Case (varX) idX
                [ Alt (LitAlt (LitInt 1)) e3
                , Alt (LitAlt (LitInt 2)) e3'])
        )
    )

expectedVal5 :: CurrExpr
expectedVal5 = CurrExpr Evaluate
    (App
        (App e1
            (Case varX idX
                [ Alt (LitAlt (LitInt 1)) e2
                , Alt (LitAlt (LitInt 2)) e2'])
        )
        (App e4
            (Case varX idX
                [ Alt (LitAlt (LitInt 1)) e3
                , Alt (LitAlt (LitInt 2)) e3'])
        )
    )

check6 :: CurrExpr -> Bool
check6 (CurrExpr Evaluate (App a1 (Case (Var (Id _ TyLitInt)) (Id _ TyLitInt) alts))) =
    a1 == (App e1
            (Case (varX) idX
                [ Alt (LitAlt (LitInt 1)) e2
                , Alt (LitAlt (LitInt 2)) e2']
            )
        )
    && (length alts == 4)
    && (S.fromList (map (\(Alt (LitAlt _) e) -> e) alts) == S.fromList [e2', e3', e3, e4])
check6 _ = False

check7 :: CurrExpr -> Bool
check7 (CurrExpr Evaluate (App a1 (Case (Var (Id _ TyLitInt)) (Id _ TyLitInt) alts))) =
    a1 == (App e1
            (Case (varX) idX
                [ Alt (LitAlt (LitInt 1)) e2
                , Alt (LitAlt (LitInt 2)) e2']
            )
        )
    && (length alts == 3)
    && S.isSubsetOf (S.fromList [e3', e4]) (S.fromList (map (\(Alt (LitAlt _) e) -> e) alts))
check7 _ = False

-- mergeCurrExpr helpers

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

xN :: Name
xN = (Name "X" Nothing 0 Nothing)

idX :: Id
idX = (Id xN TyLitInt)

varX :: Expr
varX = (Var idX)

fs1N :: Name
fs1N = (Name "fs" Nothing 0 Nothing)

idfs1 :: Id
idfs1 = (Id fs1N TyLitInt)

varfs1 :: Expr
varfs1 = (Var idfs1)

fs2N :: Name
fs2N = (Name "fs" Nothing 0 Nothing)

idfs2 :: Id
idfs2 = (Id fs2N TyLitInt)

varfs2 :: Expr
varfs2 = (Var idfs2)

createContext :: CurrExpr -> CurrExpr -> Maybe EE.ExprEnv -> Maybe EE.ExprEnv -> Context ()
createContext ce1 ce2 mEenv1 mEenv2 = emptyContext s1 s2 ng idX
    where
        kv = simpleKV
        eenv1 = fromMaybe EE.empty mEenv1
        eenv2 = fromMaybe EE.empty mEenv2
        s1 = createTestState kv (M.fromList []) ce1 eenv1 (PC.fromList [])
        s2 = createTestState kv (M.fromList []) ce2 eenv2 (PC.fromList [])
        ng = mkNameGen [s1, s2]


-- checkADTNumericalTests helpers
createStatePCs :: Int -> [PathConds]
createStatePCs numTests = take numTests (repeat (PC.fromList []))

yN :: Name
yN = (Name "Y" Nothing 0 Nothing)

idY :: Id
idY = (Id yN TyLitInt)

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
var1N = (Name "v1" Nothing 19 Nothing)

var1 :: Expr
var1 = Var (Id var1N ty1T)

var2N :: Name
var2N = (Name "v2" Nothing 26 Nothing)

var2 :: Expr
var2 = Var (Id var2N ty2T)

createTestPCs :: KnownValues -> [PathConds]
createTestPCs kv = [
                PC.fromList [ -- simple test
                    AssumePC idX 1 
                    (ConsCond dconA var1 True)
                    , ExtCond (mkEqIntExpr kv (varX) 1) True
                    , ExtCond (mkOrExpr kv (mkEqIntExpr kv (varX) 1) (mkEqIntExpr kv (varX) 2)) True]
              , PC.fromList [
                    AssumePC idX 1
                    (ConsCond dconA var1 False)
                    , AssumePC idX 1
                    (ConsCond dconB var1 False)
                    , ExtCond (mkEqIntExpr kv (varX) 1) True
                    , ExtCond (mkOrExpr kv (mkEqIntExpr kv (varX) 1) (mkEqIntExpr kv (varX) 2)) True]
               , PC.fromList [ -- combination of AssumePCs and other PathCond-s
                    ConsCond dconA var1 False
                    , (ConsCond dconB var1 False)
                    , AssumePC idX 1
                    (ConsCond dconA var1 False)
                    , ExtCond (mkOrExpr kv (mkEqIntExpr kv (varX) 1) (mkEqIntExpr kv (varX) 2)) True]
               , PC.fromList [ -- Set of (AssumePCs id i pc) with i == 2 should be satisfiable, hence entire PathConds should be satisfiable
                    AssumePC idX 1
                    (ConsCond dconA var1 False)
                    , AssumePC idX 1
                    (ConsCond dconB var1 False)
                    , AssumePC idX 2
                    (ConsCond dconA var1 True)
                    , AssumePC idX 2
                    (ConsCond dconB var1 False)
                    , ExtCond (mkOrExpr kv (mkEqIntExpr kv (varX) 1) (mkEqIntExpr kv (varX) 2)) True]
               , PC.fromList [
                    AssumePC idX 1
                        (ConsCond dconA var1 False)
                    , AssumePC idX 1
                        (ConsCond dconB var1 False)
                    , AssumePC idY 1
                        (ConsCond dconA var1 True)
                    , ExtCond (mkEqIntExpr kv (varX) 1) True
                    , ExtCond (mkOrExpr kv (mkEqIntExpr kv (varX) 1) (mkEqIntExpr kv (varX) 2)) True
                    , ExtCond (mkOrExpr kv (mkEqIntExpr kv (Var idY) 1) (mkEqIntExpr kv (Var idY) 2)) True]
               , PC.fromList [ -- simple nested AssumePCs
                    AssumePC idX 1
                    (AssumePC idY 1
                        (ConsCond dconA var1 True))
                    , AssumePC idX 1
                    (AssumePC idY 1
                        (ConsCond dconB var1 False))
                    , ExtCond (mkOrExpr kv (mkEqIntExpr kv (varX) 1) (mkEqIntExpr kv (varX) 2)) True
                    , ExtCond (mkOrExpr kv (mkEqIntExpr kv (Var idY) 1) (mkEqIntExpr kv (Var idY) 2)) True]
               , PC.fromList [ -- simple nested AssumePCs (negative test)
                    AssumePC idX 1
                    (AssumePC idY 1
                        (ConsCond dconA var1 False))
                    , AssumePC idX 1
                    (AssumePC idY 1
                        (ConsCond dconB var1 False))
                    , ExtCond (mkEqIntExpr kv (varX) 1) True
                    , ExtCond (mkEqIntExpr kv (Var idY) 1) True
                    , ExtCond (mkOrExpr kv (mkEqIntExpr kv (varX) 1) (mkEqIntExpr kv (varX) 2)) True
                    , ExtCond (mkOrExpr kv (mkEqIntExpr kv (Var idY) 1) (mkEqIntExpr kv (Var idY) 2)) True]
                -- more complex nested AssumePCs. Equivalent to (x=1 => ((y=1 => B) || (y=2 => not A && not B))) || (x=2 => ((y=1 => not A && not B))) 
               , PC.fromList [
                    AssumePC idX 1
                    (AssumePC idY 1
                        (ConsCond dconB var1 True))
                    , AssumePC idX 1
                    (AssumePC idY 2
                        (ConsCond dconB var1 False))
                    , AssumePC idX 1
                    (AssumePC idY 2
                        (ConsCond dconA var1 False))
                    , AssumePC idX 2
                    (AssumePC idY 1
                        (ConsCond dconA var1 False))
                    , AssumePC idX 2
                    (AssumePC idY 1
                        (ConsCond dconB var1 False))
                    , ExtCond (mkOrExpr kv (mkEqIntExpr kv (varX) 1) (mkEqIntExpr kv (varX) 2)) True
                    , ExtCond (mkOrExpr kv (mkEqIntExpr kv (Var idY) 1) (mkEqIntExpr kv (Var idY) 2)) True]
               , PC.fromList [ -- Multiple solutions possible
                    AssumePC idX 1
                        (ConsCond dconB var1 True)
                    , AssumePC idX 2
                        (ConsCond dconA var1 True)
                    , ExtCond (mkOrExpr kv (mkEqIntExpr kv (varX) 1) (mkEqIntExpr kv (varX) 2)) True]
               , PC.fromList [ -- Multiple Data types
                    AssumePC idX 1
                        (ConsCond dconB var1 True)
                    , AssumePC idX 1
                        (ConsCond dconD var2 True)
                    , AssumePC idX 2
                        (ConsCond dconA var1 False)
                    , AssumePC idX 2
                        (ConsCond dconA var1 True)
                    , ExtCond (mkOrExpr kv (mkEqIntExpr kv (varX) 1) (mkEqIntExpr kv (varX) 2)) True]
               ]

checkADTNumExpected :: [(TestNum, Result -> Bool)]
checkADTNumExpected = [(1, (== SAT)), (2, (== UNSAT)), (3, (== UNSAT)), (4, (== SAT)), (5, (== UNSAT)), (6, (== SAT))
                      , (7, (== UNSAT)), (8, (== SAT)), (9, (== SAT)), (10, (== SAT))]

-- solveRelAssumeTests
createTestIds :: [[Id]]
createTestIds = [ [Id var1N ty1T]
                , [Id var1N ty1T]
                , [Id var1N ty1T]
                , [Id var1N ty1T]
                , [Id var1N ty1T]
                , [Id var1N ty1T]
                , [Id var1N ty1T]
                , [Id var1N ty1T]
                , [Id var1N ty1T]
                , [Id var1N ty1T, Id var2N ty2T]
                ]

-- TODO: multiple solutions possible, add all of them
solveADTNumExpected :: [(TestNum, (Result, Maybe Model) -> Bool)]
solveADTNumExpected = [ (1, (== (SAT, Just (M.fromList [(var1N, Data dconA),(xN, Lit (LitInt 1))]))))
                      , (2, (== (UNSAT, Nothing)))
                      , (3, (== (UNSAT, Nothing)))
                      , (4, (== (SAT, Just (M.fromList [(var1N, Data dconA), (xN, Lit (LitInt 2))]))))
                      , (5, (== (UNSAT, Nothing)))
                      , (6, (== (SAT, Just (M.fromList [(var1N, Data dconB), (xN, Lit (LitInt 2)), (yN, Lit (LitInt 1))]))))
                      , (7, (== (UNSAT, Nothing)))
                      , (8, (== (SAT, Just (M.fromList [(var1N, Data dconA), (xN, Lit (LitInt 2)), (yN, Lit (LitInt 2))]))))
                      , (9, (== (SAT, Just (M.fromList [(var1N, Data dconB), (xN, Lit (LitInt 1))]))))
                      , (10, (== (SAT, Just (M.fromList [(var1N, Data dconB), (var2N, Data dconD)
                        , (xN, Lit (LitInt 1))]))))
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

            , KV.tyChar = (Name "" Nothing 0 Nothing)
            , KV.dcChar = (Name "" Nothing 0 Nothing)

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
    (mb_modname, exg2) <- translateLoaded [proj] [src] [] simplTranslationConfig config

    let (init_state, _ , _) = initState exg2 False (T.pack entry) mb_modname (mkCurrExpr Nothing Nothing) config
    return (init_state)

createTestState :: KnownValues -> TypeEnv -> CurrExpr -> EE.ExprEnv -> PathConds -> State ()
createTestState kv tenv currExpr eenv pc = State {
      expr_env = eenv
    , type_env = tenv
    , curr_expr = currExpr
    , path_conds = pc
    , non_red_path_conds = []
    , true_assert = True
    , assert_ids = Nothing
    , type_classes = TC.initTypeClasses []
    , symbolic_ids = HS.empty
    , exec_stack = Stack.empty
    , model = M.empty
    , known_values = kv
    , rules = []
    , num_steps = 0
    , track = ()
    , tags = HS.empty
    }

createTestStates :: KnownValues -> [PathConds] -> [State ()]
createTestStates kv pcs = map (createTestState kv (M.fromList [(ty1N, ty1), (ty2N, ty2)]) defaultCE EE.empty) pcs
    where defaultCE = (CurrExpr Evaluate (Lit (LitInt 0)))

createTestBindings :: Bindings
createTestBindings = Bindings {
    deepseq_walkers = M.empty
    , fixed_inputs = []
    , arb_value_gen = arbValueInit
    , cleaned_names = HM.empty
    , input_names = []
    , higher_order_inst = []
    , rewrite_rules = []
    , name_gen = mkNameGen [ty1N, ty2N, (Name "A" Nothing 17 Nothing), (Name "B" Nothing 18 Nothing), (Name "X" Nothing 0 Nothing)
        , (Name "Y" Nothing 0 Nothing), (Name "Bool" Nothing 0 Nothing), (Name "" Nothing 0 Nothing), (Name "C" Nothing 24 Nothing)
        , (Name "B" Nothing 25 Nothing)]
    }

createConfig :: Config
createConfig = Config {
    smt = ConZ3
    , mode = Regular
    , base = []
    , baseInclude = []
    , extraDefaultInclude = []
    , extraDefaultMods = []
    , logStates = Nothing
    , maxOutputs = Nothing
    , printCurrExpr = False
    , printExprEnv = False
    , printRelExprEnv = False
    , printPathCons = False
    , returnsTrue = False
    , higherOrderSolver = AllFuncs
    , stateMerging = False
    , steps = 0
    , cut_off = 0
    , switch_after = 0
    , strict = False
    , sharing = Sharing
    , timeLimit = 0
    , validate = False}

