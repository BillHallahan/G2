{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This contains functions to switch from
-- (1) A State/Exprs/Types to SMTHeaders/SMTASTs/Sorts
-- (2) SMTHeaders/SMTASTs/Sorts to some SMT solver interface
-- (3) SMTASTs/Sorts to Exprs/Types
module G2.Solver.Converters
    ( toSMTHeaders
    , toSolverText
    , exprToSMT --WOULD BE NICE NOT TO EXPORT THIS
    , typeToSMT --WOULD BE NICE NOT TO EXPORT THIS
    , toSolverAST --WOULD BE NICE NOT TO EXPORT THIS
    , sortName
    , smtastToExpr
    , modelAsExpr

    , addHeaders
    , checkConstraintsPC
    , checkModelPC
    , checkConstraints
    , solveConstraints
    , constraintsToModelOrUnsatCore
    , constraintsToModelOrUnsatCoreNoReset
    , SMTConverter (..) ) where

import qualified Data.Bits as Bits
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Int
import qualified Data.Map as M
import Data.Monoid
import Data.Ratio
import qualified Data.Text as T
import GHC.Float
import qualified Text.Builder as TB

import G2.Language hiding (Assert, vars)
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC
import G2.Solver.Language
import G2.Solver.Solver

-- | Used to describe the specific output format required by various solvers
-- By defining these functions, we can automatically convert from the SMTHeader and SMTAST
-- datatypes, to a form understandable by the solver.
class Solver con => SMTConverter con where
    closeIO :: con -> IO ()

    reset :: con -> IO ()

    checkSatInstr :: con -> IO ()
    maybeCheckSatResult :: con -> IO (Maybe (Result () () ()))

    getModelInstrResult :: con -> [(SMTName, Sort)] -> IO SMTModel
    getUnsatCoreInstrResult :: con -> IO UnsatCore

    setProduceUnsatCores :: con -> IO ()

    addFormula :: con -> [SMTHeader] -> IO ()

    checkSatNoReset :: con -> [SMTHeader] -> IO (Result () () ())
    checkSatGetModelOrUnsatCoreNoReset :: con -> [SMTHeader] -> [(SMTName, Sort)] -> IO (Result SMTModel UnsatCore ())

    checkSat :: con -> [SMTHeader] -> IO (Result () () ())
    checkSat con headers = do
        reset con
        checkSatNoReset con headers
    checkSatGetModel :: con -> [SMTHeader] -> [(SMTName, Sort)] -> IO (Result SMTModel () ())
    checkSatGetModelOrUnsatCore :: con -> [SMTHeader] -> [(SMTName, Sort)] -> IO (Result SMTModel UnsatCore ())
    checkSatGetModelOrUnsatCore con out get = do
        reset con
        setProduceUnsatCores con
        checkSatGetModelOrUnsatCoreNoReset con out get

    -- Incremental
    push :: con -> IO ()
    pop :: con -> IO ()

addHeaders :: SMTConverter con => con -> [SMTHeader] -> IO ()
addHeaders = addFormula

checkConstraintsPC :: SMTConverter con => con -> PathConds -> IO (Result () () ())
checkConstraintsPC con pc = do
    let headers = toSMTHeaders pc
    checkConstraints con headers

checkConstraints :: SMTConverter con => con -> [SMTHeader] -> IO (Result () () ())
checkConstraints = checkSat

-- | Checks if the constraints are satisfiable, and returns a model if they are
checkModelPC :: SMTConverter con => ArbValueFunc -> con -> State t -> Bindings -> [Id] -> PathConds -> IO (Result Model () ())
checkModelPC avf con s b is pc = return . liftCasts =<< checkModel' avf con s b is pc

-- | We split based on whether we are evaluating a ADT or a literal.
-- ADTs can be solved using our efficient addADTs, while literals require
-- calling an SMT solver.
checkModel' :: SMTConverter con => ArbValueFunc -> con -> State t -> Bindings -> [Id] -> PathConds -> IO (Result Model () ())
checkModel' _ _ s _ [] _ = do
    return (SAT $ model s)
checkModel' avf con s b (i:is) pc
    | (idName i) `HM.member` (model s) = checkModel' avf con s b is pc
    | otherwise =  do
        (m, av) <- getModelVal avf con s b i pc
        case m of
            SAT m' -> checkModel' avf con (s {model = HM.union m' (model s)}) (b {arb_value_gen = av}) is pc
            r -> return r

getModelVal :: SMTConverter con => ArbValueFunc -> con -> State t -> Bindings -> Id -> PathConds -> IO (Result Model () (), ArbValueGen)
getModelVal avf con (State { expr_env = eenv, type_env = tenv, known_values = kv }) b (Id n _) pc = do
    let (Just (Var (Id n' t))) = E.lookup n eenv
     
    case PC.null pc of
                True -> 
                    let
                        (e, av) = avf t tenv (arb_value_gen b)
                    in
                    return (SAT $ HM.singleton n' e, av) 
                False -> do
                    m <- solveNumericConstraintsPC con kv tenv pc
                    return (m, arb_value_gen b)

solveNumericConstraintsPC :: SMTConverter con => con -> KnownValues -> TypeEnv -> PathConds -> IO (Result Model () ())
solveNumericConstraintsPC con kv tenv pc = do
    let headers = toSMTHeaders pc
    let vs = map (\(n', srt) -> (nameToStr n', srt)) . HS.toList . pcVars $ pc

    m <- solveConstraints con headers vs
    case m of
        SAT m' -> return . SAT $ modelAsExpr kv tenv m'
        UNSAT () -> return $ UNSAT ()
        Unknown s () -> return $ Unknown s ()

solveConstraints :: SMTConverter con => con -> [SMTHeader] -> [(SMTName, Sort)] -> IO (Result SMTModel () ())
solveConstraints con headers vs = checkSatGetModel con headers vs

constraintsToModelOrUnsatCore :: SMTConverter con => con -> [SMTHeader] -> [(SMTName, Sort)] -> IO (Result SMTModel UnsatCore ())
constraintsToModelOrUnsatCore = checkSatGetModelOrUnsatCore

constraintsToModelOrUnsatCoreNoReset :: SMTConverter con => con -> [SMTHeader] -> [(SMTName, Sort)] -> IO (Result SMTModel UnsatCore ())
constraintsToModelOrUnsatCoreNoReset = checkSatGetModelOrUnsatCoreNoReset

-- | Here we convert from a State, to an SMTHeader.  This SMTHeader can later
-- be given to an SMT solver by using toSolver.
-- To determine the input that can be fed to a state to get the curr_expr,
-- we need only consider the types and path constraints of that state.
-- We can also pass in some other Expr Container to instantiate names from, which is
-- important if you wish to later be able to scrape variables from those Expr's
toSMTHeaders :: PathConds -> [SMTHeader]
toSMTHeaders = addSetLogic . toSMTHeaders'

toSMTHeaders' :: PathConds -> [SMTHeader]
toSMTHeaders' pc  =
    let
        pc' = PC.toList pc
    in 
    (pcVarDecls pc)
    ++
    (pathConsToSMTHeaders pc')

-- |  Determines an appropriate SetLogic command, and adds it to the headers
addSetLogic :: [SMTHeader] -> [SMTHeader]
addSetLogic xs =
    let
        lia = isLIA xs
        lra = isLRA xs
        lira = isLIRA xs
        nia = isNIA xs
        nra = isNRA xs
        nira = isNIRA xs
        uflia = isUFLIA xs

        sl = if lia then SetLogic QF_LIA else
             if lra then SetLogic QF_LRA else
             if lira then SetLogic QF_LIRA else
             if nia then SetLogic QF_NIA else
             if nra then SetLogic QF_NRA else 
             if nira then SetLogic QF_NIRA else
             if uflia then SetLogic QF_UFLIA else SetLogic ALL
    in
    sl:xs

isNIA :: (ASTContainer m SMTAST) => m -> Bool
isNIA = getAll . evalASTs isNIA'

isNIA' :: SMTAST -> All
isNIA' (_ :* _) = All True
isNIA' (_ :/ _) = All True
isNIA' (_ `Modulo` _) = All True
isNIA' s = isLIA' s

isLIA :: (ASTContainer m SMTAST) => m -> Bool
isLIA = getAll . evalASTs isLIA'

isLIA' :: SMTAST -> All
isLIA' (_ :>= _) = All True
isLIA' (_ :> _) = All True
isLIA' (_ := _) = All True
isLIA' (_ :/= _) = All True
isLIA' (_ :< _) = All True
isLIA' (_ :<= _) = All True
isLIA' (_ :+ _) = All True
isLIA' (_ :- _) = All True
isLIA' (x :* y) = All $ isIntegerCoeff x || isIntegerCoeff y
isLIA' (Neg _) = All True
isLIA' (VInt _) = All True
isLIA' (V _ s) = All $ isIASort s
isLIA' s = isCore' s

isIASort :: Sort -> Bool
isIASort SortInt = True
isIASort s = isCoreSort s

isIntegerCoeff :: SMTAST -> Bool
isIntegerCoeff (Neg s) = isIntegerCoeff s
isIntegerCoeff (VInt _) = True
isIntegerCoeff _ = False

isNRA :: (ASTContainer m SMTAST) => m -> Bool
isNRA = getAll . evalASTs isNRA'

isNRA' :: SMTAST -> All
isNRA' (_ :* _) = All True
isNRA' (_ :/ _) = All True
isNRA' s = isLRA' s

isLRA :: (ASTContainer m SMTAST) => m -> Bool
isLRA = getAll . evalASTs isLRA'

isLRA' :: SMTAST -> All
isLRA' (_ :>= _) = All True
isLRA' (_ :> _) = All True
isLRA' (_ := _) = All True
isLRA' (_ :/= _) = All True
isLRA' (_ :< _) = All True
isLRA' (_ :<= _) = All True
isLRA' (_ :+ _) = All True
isLRA' (_ :- _) = All True
isLRA' (x :* y) = All $ isRationalCoeff x || isRationalCoeff y
isLRA' (Neg _) = All True
isLRA' (V _ s) = All $ isRASort s
isLRA' s = isCore' s

isRASort :: Sort -> Bool
isRASort s = isCoreSort s

isRationalCoeff :: SMTAST -> Bool
isRationalCoeff (Neg s) = isRationalCoeff s
isRationalCoeff (VFloat _) = True
isRationalCoeff (VDouble _) = True
isRationalCoeff _ = False

isLIRA :: (ASTContainer m SMTAST) => m -> Bool
isLIRA = getAll . evalASTs isLIRA'

isLIRA' :: SMTAST -> All
isLIRA' (ItoR _) = All True
isLIRA' s = All $ getAll (isLIA' s) || getAll (isLRA' s)

isNIRA :: (ASTContainer m SMTAST) => m -> Bool
isNIRA = getAll . evalASTs isNIRA'

isNIRA' :: SMTAST -> All
isNIRA' (ItoR _) = All True
isNIRA' s = All $ getAll (isNIA' s) || getAll (isNRA' s)

isUFLIA :: (ASTContainer m SMTAST) => m -> Bool
isUFLIA = getAll . evalASTs isUFLIA'

isUFLIA' :: SMTAST -> All
isUFLIA' (Func _ xs) = mconcat $ map isUFLIA' xs
isUFLIA' s = isLIA' s

isCore' :: SMTAST -> All
isCore' (_ := _) = All True
isCore' (SmtAnd _) = All True
isCore' (SmtOr _) = All True
isCore' ((:!) _) = All True
isCore' (_ :=> _) = All True
isCore' (_ :<=> _) = All True
isCore' (Func _ _) = All True
isCore' (VBool _) = All True
isCore' (V _ s) = All $ isCoreSort s
isCore' _ = All False

isCoreSort :: Sort -> Bool
isCoreSort SortBool = True
isCoreSort _ = False

-------------------------------------------------------------------------------

pathConsToSMTHeaders :: [PathCond] -> [SMTHeader]
pathConsToSMTHeaders = map pathConsToSMT

pathConsToSMT :: PathCond -> SMTHeader
pathConsToSMT (MinimizePC e) = Minimize $ exprToSMT e
pathConsToSMT (SoftPC pc) = AssertSoft (pathConsToSMT' pc) Nothing
pathConsToSMT pc = Assert (pathConsToSMT' pc) 

pathConsToSMT' :: PathCond -> SMTAST
pathConsToSMT' (AltCond l e b) =
    let
        exprSMT = exprToSMT e
        altSMT = altToSMT l e
    in
    if b then exprSMT := altSMT else (:!) (exprSMT := altSMT) 
pathConsToSMT' (ExtCond e b) =
    let
        exprSMT = exprToSMT e
    in
    if b then exprSMT else (:!) exprSMT
pathConsToSMT' (AssumePC (Id n t) num pc) =
    let
        idSMT = V (nameToStr n) (typeToSMT t) -- exprToSMT (Var i)
        intSMT = VInt $ toInteger num -- exprToSMT (Lit (LitInt $ toInteger num))
        pcSMT = map (pathConsToSMT' . PC.unhashedPC) $ HS.toList pc
    in
    (idSMT := intSMT) :=> SmtAnd pcSMT
pathConsToSMT' (MinimizePC _) = error "pathConsToSMT': unsupported nesting of MinimizePC."
pathConsToSMT' (SoftPC _) = error "pathConsToSMT': unsupported nesting of SoftPC."

exprToSMT :: Expr -> SMTAST
exprToSMT (Var (Id n t)) = V (nameToStr n) (typeToSMT t)
exprToSMT (Lit c) =
    case c of
        LitInt i -> VInt i
        LitFloat f -> VFloat f
        LitDouble d -> VDouble d
        LitChar ch -> VChar ch
        err -> error $ "exprToSMT: invalid Expr: " ++ show err
exprToSMT (Data (DataCon n (TyCon (Name "Bool" _ _ _) _))) =
    case nameOcc n of
        "True" -> VBool True
        "False" -> VBool False
        _ -> error "Invalid bool in exprToSMT"
exprToSMT (Data (DataCon n t)) = V (nameToStr n) (typeToSMT t)
exprToSMT a@(App _ _) =
    let
        f = getFunc a
        ars = getArgs a
    in
    funcToSMT f ars
    where
        getFunc :: Expr -> Expr
        getFunc v@(Var _) = v
        getFunc p@(Prim _ _) = p
        getFunc (App a' _) = getFunc a'
        getFunc d@(Data _) = d 
        getFunc err = error $ "getFunc: invalid Expr: " ++ show err

        getArgs :: Expr -> [Expr]
        getArgs (App a1 a2) = getArgs a1 ++ [a2]
        getArgs _ = []
exprToSMT e = error $ "exprToSMT: unhandled Expr: " ++ show e

-- | We split based on whether the passed Expr is a function or known data constructor, or an unknown data constructor
funcToSMT :: Expr -> [Expr] -> SMTAST
funcToSMT (Prim p _) [a] = funcToSMT1Prim p a
funcToSMT (Prim p _) [a1, a2] = funcToSMT2Prim p a1 a2
funcToSMT e l = error ("Unrecognized " ++ show e ++ " with args " ++ show l ++ " in funcToSMT")

funcToSMT1Prim :: Primitive -> Expr -> SMTAST
funcToSMT1Prim Negate a = Neg (exprToSMT a)
funcToSMT1Prim FpNeg a = FpNegSMT (exprToSMT a)
funcToSMT1Prim FpSqrt e = FpSqrtSMT (exprToSMT e)
funcToSMT1Prim IsNaN e = IsNaNSMT (exprToSMT e)
funcToSMT1Prim Abs e = AbsSMT (exprToSMT e)
funcToSMT1Prim Not e = (:!) (exprToSMT e)
funcToSMT1Prim IntToFloat e = ItoR (exprToSMT e)
funcToSMT1Prim IntToDouble e = ItoR (exprToSMT e)
funcToSMT1Prim IntToString e = FromInt (exprToSMT e)
funcToSMT1Prim Chr e = FromCode (exprToSMT e)
funcToSMT1Prim OrdChar e = ToCode (exprToSMT e)
funcToSMT1Prim StrLen e = StrLenSMT (exprToSMT e)
funcToSMT1Prim err _ = error $ "funcToSMT1Prim: invalid Primitive " ++ show err

funcToSMT2Prim :: Primitive -> Expr -> Expr -> SMTAST
funcToSMT2Prim And a1 a2 = SmtAnd [exprToSMT a1, exprToSMT a2]
funcToSMT2Prim Or a1 a2 = SmtOr [exprToSMT a1, exprToSMT a2]
funcToSMT2Prim Implies a1 a2 = exprToSMT a1 :=> exprToSMT a2
funcToSMT2Prim Iff a1 a2 = exprToSMT a1 :<=> exprToSMT a2
funcToSMT2Prim Ge a1 a2 = exprToSMT a1 :>= exprToSMT a2
funcToSMT2Prim Gt a1 a2 = exprToSMT a1 :> exprToSMT a2
funcToSMT2Prim Eq a1 a2 = exprToSMT a1 := exprToSMT a2
funcToSMT2Prim Neq a1 a2 = exprToSMT a1 :/= exprToSMT a2
funcToSMT2Prim Lt a1 a2 = exprToSMT a1 :< exprToSMT a2
funcToSMT2Prim Le a1 a2 = exprToSMT a1 :<= exprToSMT a2
funcToSMT2Prim Plus a1 a2 = exprToSMT a1 :+ exprToSMT a2
funcToSMT2Prim Minus a1 a2 = exprToSMT a1 :- exprToSMT a2
funcToSMT2Prim Mult a1 a2 = exprToSMT a1 :* exprToSMT a2
funcToSMT2Prim Div a1 a2 = exprToSMT a1 :/ exprToSMT a2

funcToSMT2Prim FpAdd a1 a2 = exprToSMT a1 `FpAddSMT` exprToSMT a2
funcToSMT2Prim FpSub a1 a2 = exprToSMT a1 `FpSubSMT` exprToSMT a2
funcToSMT2Prim FpMul a1 a2 = exprToSMT a1 `FpMulSMT` exprToSMT a2
funcToSMT2Prim FpDiv a1 a2 = exprToSMT a1 `FpDivSMT` exprToSMT a2

funcToSMT2Prim FpLeq a1 a2 = exprToSMT a1 `FpLeqSMT` exprToSMT a2
funcToSMT2Prim FpLt a1 a2 = exprToSMT a1 `FpLtSMT` exprToSMT a2
funcToSMT2Prim FpGeq a1 a2 = exprToSMT a1 `FpGeqSMT` exprToSMT a2
funcToSMT2Prim FpGt a1 a2 = exprToSMT a1 `FpGtSMT` exprToSMT a2
funcToSMT2Prim FpEq a1 a2 = exprToSMT a1 `FpEqSMT` exprToSMT a2
funcToSMT2Prim FpNeq a1 a2 = (:!) (exprToSMT a1 `FpEqSMT` exprToSMT a2)

funcToSMT2Prim Quot a1 a2 = exprToSMT a1 `QuotSMT` exprToSMT a2
funcToSMT2Prim Mod a1 a2 = exprToSMT a1 `Modulo` exprToSMT a2
funcToSMT2Prim Rem a1 a2 = exprToSMT a1 :- ((exprToSMT a1 `QuotSMT` exprToSMT a2) :* exprToSMT a2) -- TODO: more efficient encoding?
funcToSMT2Prim RationalToDouble a1 a2  = exprToSMT a1 :/ exprToSMT a2
funcToSMT2Prim StrAppend a1 a2  = exprToSMT a1 :++ exprToSMT a2
funcToSMT2Prim op lhs rhs = error $ "funcToSMT2Prim: invalid case with (op, lhs, rhs): " ++ show (op, lhs, rhs)

altToSMT :: Lit -> Expr -> SMTAST
altToSMT (LitInt i) _ = VInt i
altToSMT (LitFloat f) _ = VFloat f
altToSMT (LitDouble d) _ = VDouble d
altToSMT (LitChar c) _ = VChar c
altToSMT am _ = error $ "Unhandled " ++ show am

createUniqVarDecls :: [(Name, Sort)] -> [SMTHeader]
createUniqVarDecls [] = []
createUniqVarDecls ((n,SortChar):xs) =
    let
        lenAssert = Assert $ StrLenSMT (V (nameToStr n) SortChar) := VInt 1
    in
    VarDecl (nameToBuilder n) SortChar:lenAssert:createUniqVarDecls xs
createUniqVarDecls ((n,s):xs) = VarDecl (nameToBuilder n) s:createUniqVarDecls xs

pcVarDecls :: PathConds -> [SMTHeader]
pcVarDecls = createUniqVarDecls . HS.toList . pcVars

-- Get's all variable required for a list of `PathCond` 
pcVars :: PathConds -> HS.HashSet (Name, Sort)
pcVars = HS.map idToNameSort . PC.allIds

idToNameSort :: Id -> (Name, Sort)
idToNameSort (Id n t) = (n, typeToSMT t)

typeToSMT :: Type -> Sort
typeToSMT (TyFun TyLitInt _) = SortInt -- TODO: Remove this
typeToSMT (TyFun TyLitDouble _) = SortDouble -- TODO: Remove this
typeToSMT (TyFun TyLitFloat _) = SortFloat -- TODO: Remove this
typeToSMT TyLitInt = SortInt
typeToSMT TyLitDouble = SortDouble
typeToSMT TyLitFloat = SortFloat
typeToSMT TyLitChar = SortChar
typeToSMT (TyCon (Name "Bool" _ _ _) _) = SortBool
#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
typeToSMT (TyApp (TyCon (Name "List" _ _ _) _) (TyCon (Name "Char" _ _ _) _)) = SortString
#else
typeToSMT (TyApp (TyCon (Name "[]" _ _ _) _) (TyCon (Name "Char" _ _ _) _)) = SortString
#endif
typeToSMT t = error $ "Unsupported type in typeToSMT: " ++ show t

merge :: TB.Builder -> TB.Builder -> TB.Builder
merge x y = x <> "\n" <> y

comment :: String -> TB.Builder
comment s = "; " <> TB.string s

assertSoftSolver :: TB.Builder -> Maybe T.Text -> TB.Builder
assertSoftSolver ast Nothing = function1 "assert-soft" ast
assertSoftSolver ast (Just lab) = "(assert-soft " <> ast <> " :id " <> TB.text lab <> ")"

defineFun :: String -> [(String, Sort)] -> Sort -> SMTAST -> TB.Builder
defineFun fn ars ret body =
    "(define-fun " <> (TB.string fn) <> " ("
        <> TB.intercalate " " (map (\(n, s) -> "(" <> TB.string n <> " " <> sortName s <> ")") ars) <> ")"
        <> " (" <> sortName ret <> ") " <> toSolverAST body <> ")"

declareFun :: String -> [Sort] -> Sort -> TB.Builder
declareFun fn ars ret =
    "(declare-fun " <> TB.string fn <> " ("
        <> TB.intercalate " " (map sortName ars) <> ")"
        <> " (" <> sortName ret <> "))"

toSolverText :: [SMTHeader] -> TB.Builder
toSolverText [] = ""
toSolverText (Assert ast:xs) = 
    merge (function1 "assert" $ toSolverAST ast) (toSolverText xs)
toSolverText (AssertSoft ast lab:xs) = 
    merge (assertSoftSolver (toSolverAST ast) lab) (toSolverText xs)
toSolverText (Minimize ast:xs) =
    merge (function1 "minimize" $ toSolverAST ast) (toSolverText xs)
toSolverText (DefineFun f ars ret body:xs) =
    merge (defineFun f ars ret body) (toSolverText xs)
toSolverText (DeclareFun f ars ret:xs) =
    merge (declareFun f ars ret) (toSolverText xs)
toSolverText (VarDecl n s:xs) = merge (toSolverVarDecl n s) (toSolverText xs)
toSolverText (SetLogic lgc:xs) = merge (toSolverSetLogic lgc) (toSolverText xs)
toSolverText (Comment c:xs) = merge (comment c) (toSolverText xs)

toSolverAST :: SMTAST -> TB.Builder
toSolverAST (x :>= y) = function2 ">=" (toSolverAST x) (toSolverAST y)
toSolverAST (x :> y) = function2 ">" (toSolverAST x) (toSolverAST y)
toSolverAST (x := y) = function2 "=" (toSolverAST x) (toSolverAST y)
toSolverAST (x :/= y) = function1 "not" $ function2 "=" (toSolverAST x) (toSolverAST y)
toSolverAST (x :< y) = function2 "<" (toSolverAST x) (toSolverAST y)
toSolverAST (x :<= y) = function2 "<=" (toSolverAST x) (toSolverAST y)

toSolverAST (SmtAnd []) = "true"
toSolverAST (SmtAnd [x]) = toSolverAST x
toSolverAST (SmtAnd xs) = functionList "and" $ map (toSolverAST) xs
toSolverAST (SmtOr []) = "false"
toSolverAST (SmtOr [x]) = toSolverAST x
toSolverAST (SmtOr xs) =  functionList "or" $ map (toSolverAST) xs

toSolverAST ((:!) x) = function1 "not" $ toSolverAST x
toSolverAST (x :=> y) = function2 "=>" (toSolverAST x) (toSolverAST y)
toSolverAST (x :<=> y) = function2 "=" (toSolverAST x) (toSolverAST y)

toSolverAST (x :+ y) = function2 "+" (toSolverAST x) (toSolverAST y)
toSolverAST (x :- y) = function2 "-" (toSolverAST x) (toSolverAST y)
toSolverAST (x :* y) = function2 "*" (toSolverAST x) (toSolverAST y)
toSolverAST (x :/ y) = function2 "/" (toSolverAST x) (toSolverAST y)
toSolverAST (x `QuotSMT` y) = function2 "div" (toSolverAST x) (toSolverAST y)
toSolverAST (x `Modulo` y) = function2 "mod" (toSolverAST x) (toSolverAST y)
toSolverAST (AbsSMT x) = "(abs " <> toSolverAST x <> ")"
toSolverAST (SqrtSMT x) = "(^ " <> toSolverAST x <> " 0.5)"
toSolverAST (Neg x) = function1 "-" $ toSolverAST x

toSolverAST (FpNegSMT x) = function1 "fp.neg" (toSolverAST x)
toSolverAST (FpAddSMT x y) = function3 "fp.add" "RNE" (toSolverAST x) (toSolverAST y)
toSolverAST (FpSubSMT x y) = function3 "fp.sub" "RNE" (toSolverAST x) (toSolverAST y)
toSolverAST (FpMulSMT x y) = function3 "fp.mul" "RNE" (toSolverAST x) (toSolverAST y)
toSolverAST (FpDivSMT x y) = function3 "fp.div" "RNE" (toSolverAST x) (toSolverAST y)

toSolverAST (FpLeqSMT x y) = function2 "fp.leq" (toSolverAST x) (toSolverAST y)
toSolverAST (FpLtSMT x y) = function2 "fp.lt" (toSolverAST x) (toSolverAST y)
toSolverAST (FpGeqSMT x y) = function2 "fp.geq" (toSolverAST x) (toSolverAST y)
toSolverAST (FpGtSMT x y) = function2 "fp.gt" (toSolverAST x) (toSolverAST y)
toSolverAST (FpEqSMT x y) = function2 "fp.eq" (toSolverAST x) (toSolverAST y)

toSolverAST (FpSqrtSMT x) = function2 "fp.sqrt" "RNE" (toSolverAST x)
toSolverAST (IsNaNSMT x) = function1 "fp.isNaN" (toSolverAST x)

toSolverAST (ArrayConst v indS valS) =
    let
        sort_arr = "(Array " <> sortName indS <> " " <> sortName valS <> ")"
    in
    "((as const " <> sort_arr <> ") " <> (toSolverAST v) <> ")"

toSolverAST (ArraySelect arr ind) =
    function2 "select" (toSolverAST arr) (toSolverAST ind)

toSolverAST (ArrayStore arr ind val) =
    function3 "store" (toSolverAST arr) (toSolverAST ind) (toSolverAST val)

toSolverAST (Func n xs) = smtFunc n $ map (toSolverAST) xs

toSolverAST (x :++ y) = function2 "str.++" (toSolverAST x) (toSolverAST y)
toSolverAST (FromInt x) = function1 "str.from_int" $ toSolverAST x
toSolverAST (StrLenSMT x) = function1 "str.len" $ toSolverAST x
toSolverAST (ItoR x) = function1 "to_real" $ toSolverAST x

toSolverAST (Ite x y z) =
    function3 "ite" (toSolverAST x) (toSolverAST y) (toSolverAST z)

toSolverAST (FromCode chr) = function1 "str.from_code" (toSolverAST chr)
toSolverAST (ToCode chr) = function1 "str.to_code" (toSolverAST chr)

toSolverAST (VInt i) = if i >= 0 then showText i else "(- " <> showText (abs i) <> ")"
toSolverAST (VFloat f) =
    let
        w32 = convertBits $ castFloatToWord32 f
        h:_ = w32
        eb = take 8 $ drop 1 w32
        sb = drop 9 w32
    in
    "(fp #b" <> TB.char h <> " #b" <> TB.string eb <> " #b" <> TB.string sb <> ")"
toSolverAST (VDouble d) = if d >= 0 then showText d else "(- " <> showText (abs d) <> ")"
toSolverAST (VChar c) = "\"" <> TB.string [c] <> "\""
toSolverAST (VBool b) = if b then "true" else "false"
toSolverAST (V n _) = TB.string n

toSolverAST (Named x n) = "(! " <> toSolverAST x <> " :named " <> TB.string n <> ")"

toSolverAST ast = error $ "toSolverAST: invalid SMTAST: " ++ show ast

-- | Convert to a little endian list of bits
convertBits :: (Num b, Bits.FiniteBits b) => b -> String
convertBits b = map (\x -> if x then '1' else '0') . reverse $ map (Bits.testBit b) [0..Bits.finiteBitSize b - 1]

smtFunc :: String -> [TB.Builder] -> TB.Builder
smtFunc n [] = TB.string n
smtFunc n xs = "(" <> TB.string n <> " " <> TB.intercalate " " xs <>  ")"

{-# INLINE showText #-}
showText :: Show a => a -> TB.Builder
showText = TB.string . show

functionList :: TB.Builder -> [TB.Builder] -> TB.Builder
functionList f xs = "(" <> f <> " " <> (TB.intercalate " " xs) <> ")" 

function1 :: TB.Builder -> TB.Builder -> TB.Builder
function1 f a = "(" <> f <> " " <> a <> ")"

{-# INLINE function2 #-}
function2 :: TB.Builder -> TB.Builder -> TB.Builder -> TB.Builder
function2 f a b = "(" <> f <> " " <> a <> " " <> b <> ")"

function3 :: TB.Builder -> TB.Builder -> TB.Builder -> TB.Builder -> TB.Builder
function3 f a b c = "(" <> f <> " " <> a <> " " <> b <> " " <> c <> ")"

toSolverVarDecl :: SMTNameBldr -> Sort -> TB.Builder
toSolverVarDecl n s = "(declare-const " <> n <> " " <> sortName s <> ")"

sortName :: Sort -> TB.Builder
sortName SortInt = "Int"
sortName SortFloat = "Float32"
sortName SortDouble = "Float64"
sortName SortString = "String"
sortName SortChar = "String"
sortName SortBool = "Bool"
sortName (SortArray ind val) = "(Array " <> sortName ind <> " " <> sortName val <> ")"
sortName _ = error "sortName: unsupported Sort"

toSolverSetLogic :: Logic -> TB.Builder
toSolverSetLogic lgc =
    let
        s = case lgc of
            QF_LIA -> "QF_LIA"
            QF_LRA -> "QF_LRA"
            QF_LIRA -> "QF_LIRA"
            QF_NIA -> "QF_NIA"
            QF_NRA -> "QF_NRA"
            QF_NIRA -> "QF_NIRA"
            QF_UFLIA -> "QF_UFLIA"
            _ -> "ALL"
    in
    "(set-logic " <> s <> ")"

-- | Converts an `SMTAST` to an `Expr`.
smtastToExpr :: KnownValues -> TypeEnv -> SMTAST -> Expr
smtastToExpr _ _ (VInt i) = (Lit $ LitInt i)
smtastToExpr _ _ (VFloat f) = (Lit $ LitFloat f)
smtastToExpr _ _ (VDouble d) = (Lit $ LitDouble d)
smtastToExpr kv _ (VBool True) = mkTrue kv
smtastToExpr kv _ (VBool False) = mkFalse kv
smtastToExpr kv tenv (VString cs) = mkG2List kv tenv (tyChar kv) $ map (App (mkDCChar kv tenv) . Lit . LitChar) cs
smtastToExpr _ _ (VChar c) = Lit $ LitChar c
smtastToExpr _ _ (V n s) = Var $ Id (certainStrToName n) (sortToType s)
smtastToExpr _ _ _ = error "Conversion of this SMTAST to an Expr not supported."

-- | Converts a `Sort` to an `Type`.
sortToType :: Sort -> Type
sortToType (SortInt) = TyLitInt
sortToType (SortFloat) = TyLitFloat
sortToType (SortDouble) = TyLitDouble
sortToType (SortChar) = TyLitChar
sortToType (SortBool) = TyCon (Name "Bool" Nothing 0 Nothing) TYPE
sortToType _ = error "Conversion of this Sort to a Type not supported."

-- | Coverts an `SMTModel` to a `Model`.
modelAsExpr :: KnownValues -> TypeEnv ->SMTModel -> Model
modelAsExpr kv tenv = HM.fromList . M.toList . M.mapKeys strToName . M.map (smtastToExpr kv tenv)

certainStrToName :: String -> Name
certainStrToName s =
    case maybe_StrToName s of
        Just n -> n
        Nothing -> Name (T.pack s) Nothing 0 Nothing