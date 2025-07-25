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
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid hiding (Alt)
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
        str = isStr xs

        sl = if lia then SetLogic QF_LIA else
             if lra then SetLogic QF_LRA else
             if lira then SetLogic QF_LIRA else
             if nia then SetLogic QF_NIA else
             if nra then SetLogic QF_NRA else 
             if nira then SetLogic QF_NIRA else
             if uflia then SetLogic QF_UFLIA else
             if str then SetLogic QF_S else SetLogic ALL
    in
    sl:xs

-- NIA

isNIA :: (ASTContainer m SMTAST) => m -> Bool
isNIA = getAll . evalASTs isNIA'

isNIA' :: SMTAST -> All
isNIA' (_ :* _) = All True
isNIA' (_ :/ _) = All True
isNIA' (_ `Modulo` _) = All True
isNIA' (_ `QuotSMT` _) = All True
isNIA' s = isLIA' s

-- LIA

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

-- NRA

isNRA :: (ASTContainer m SMTAST) => m -> Bool
isNRA = getAll . evalASTs isNRA'

isNRA' :: SMTAST -> All
isNRA' (_ :* _) = All True
isNRA' (_ :/ _) = All True
isNRA' s = isLRA' s

-- LRA

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
isLRA' (VReal _) = All True
isLRA' (V _ s) = All $ isRASort s
isLRA' s = isCore' s

isRASort :: Sort -> Bool
isRASort SortReal = True
isRASort s = isCoreSort s

isRationalCoeff :: SMTAST -> Bool
isRationalCoeff (Neg s) = isRationalCoeff s
isRationalCoeff (VFloat _) = True
isRationalCoeff (VDouble _) = True
isRationalCoeff _ = False

-- LIRA

isLIRA :: (ASTContainer m SMTAST) => m -> Bool
isLIRA = getAll . evalASTs isLIRA'

isLIRA' :: SMTAST -> All
isLIRA' (IntToRealSMT _) = All True
isLIRA' s = All $ getAll (isLIA' s) || getAll (isLRA' s)

-- NIRA

isNIRA :: (ASTContainer m SMTAST) => m -> Bool
isNIRA = getAll . evalASTs isNIRA'

isNIRA' :: SMTAST -> All
isNIRA' s = All $ getAll (isNIA' s) || getAll (isNRA' s)

-- UFLIA

isUFLIA :: (ASTContainer m SMTAST) => m -> Bool
isUFLIA = getAll . evalASTs isUFLIA'

isUFLIA' :: SMTAST -> All
isUFLIA' (Func _ xs) = mconcat $ map isUFLIA' xs
isUFLIA' s = isLIA' s

-- Str

isStr :: (ASTContainer m SMTAST) => m -> Bool
isStr = getAll . evalASTs isStr'

isStr' :: SMTAST -> All
isStr' (_ :++ _) = All True
isStr' (FromInt _) = All True
isStr' (_ `StrLtSMT` _) = All True
isStr' (_ `StrLeSMT` _) = All True
isStr' (_ `StrGtSMT` _) = All True
isStr' (_ `StrGeSMT` _) = All True
isStr' (StrLenSMT _) = All True
isStr' (_ :!! _) = All True
isStr' (StrSubstrSMT _ _ _) = All True
isStr' (StrIndexOfSMT _ _ _) = All True
isStr' (StrReplaceSMT _ _ _) = All True
isStr' (StrPrefixOfSMT _ _) = All True
isStr' (StrSuffixOfSMT _ _) = All True
isStr' (FromCode _) = All True
isStr' (ToCode _) = All True
isStr' (VString _) = All True
isStr' (VChar _) = All True
isStr' (V _ s) = All $ isStringSort s
isStr' s = isLIA' s

isStringSort :: Sort -> Bool
isStringSort SortString = True
isStringSort SortChar = True
isStringSort s = isIASort s

-- Core

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
        LitWord i -> VWord i
        LitFloat f -> VFloat f
        LitDouble d -> VDouble d
        LitRational r -> VReal r
        LitBV bv -> VBitVec bv
        LitChar ch -> VChar ch
        LitString s -> VString s
        err -> error $ "exprToSMT: invalid Expr: " ++ show err
exprToSMT (Data (DataCon n (TyCon (Name "Bool" _ _ _) _ ) _ _)) =
    case nameOcc n of
        "True" -> VBool True
        "False" -> VBool False
        _ -> error "Invalid bool in exprToSMT"
exprToSMT (Data (DataCon n t _ _)) = V (nameToStr n) (typeToSMT t)
exprToSMT (App (Data (DataCon (Name "[]" _ _ _) _ _ _)) (Type (TyCon (Name "Char" _ _ _) _))) = VString ""
exprToSMT e | [ Data (DataCon (Name ":" _ _ _) _ _ _)
              , Type (TyCon (Name "Char" _ _ _) _)
              , App _ e1
              , e2] <- unApp e = exprToSMT e1 :++ exprToSMT e2
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
exprToSMT (Case bindee _ _ as)
    | m_ls <- map fromLitAlt as
    , all isJust m_ls
    , ((_, init_e):ls) <- catMaybes m_ls =
        let
            bindee' = exprToSMT bindee
        in
        foldr (\(i, e) -> IteSMT (bindee' := VInt i) (exprToSMT e)) (exprToSMT init_e) ls
    where
        fromLitAlt (Alt (LitAlt (LitInt i)) e) = Just (i, e)
        fromLitAlt _ = Nothing

exprToSMT e = error $ "exprToSMT: unhandled Expr: " ++ show e

-- | We split based on whether the passed Expr is a function or known data constructor, or an unknown data constructor
funcToSMT :: Expr -> [Expr] -> SMTAST
funcToSMT (Prim p _) [a] = funcToSMT1Prim p a
funcToSMT (Prim p _) [a1, a2] = funcToSMT2Prim p a1 a2
funcToSMT (Prim p _) [a1, a2, a3] = funcToSMT3Prim p a1 a2 a3
funcToSMT e l = error ("Unrecognized " ++ show e ++ " with args " ++ show l ++ " in funcToSMT")

funcToSMT1Prim :: Primitive -> Expr -> SMTAST
funcToSMT1Prim Negate a = Neg (exprToSMT a)
funcToSMT1Prim FpNeg a = FpNegSMT (exprToSMT a)
funcToSMT1Prim FpSqrt e = FpSqrtSMT (exprToSMT e)
funcToSMT1Prim TruncZero e | typeOf e == TyLitFloat = FloatToIntSMT (TruncZeroSMT (exprToSMT e))
                           | typeOf e == TyLitDouble = DoubleToIntSMT (TruncZeroSMT (exprToSMT e))
funcToSMT1Prim DecimalPart e | typeOf e == TyLitFloat = exprToSMT e `FpSubSMT` TruncZeroSMT (exprToSMT e)
                             | typeOf e == TyLitDouble = exprToSMT e `FpSubSMT` TruncZeroSMT (exprToSMT e)
funcToSMT1Prim FpIsNegativeZero e =
    let
        nz = "INTERNAL_!!_IsNegZero"
        smt_srt = typeToSMT (typeOf e) 
    in
    SLet (nz, exprToSMT e) $ SmtAnd [FpIsNegative (V nz smt_srt), FpIsZero (V nz smt_srt)]
funcToSMT1Prim IsDenormalized e =
    let
        zero = case typeOf e of
                    TyLitFloat -> VFloat 0
                    TyLitDouble -> VDouble 0
                    _ -> error "funcToSMT1Prim: bad type passed to IsDenormalized"
    in
    SmtAnd [(:!) (IsNormalSMT (exprToSMT e)), (:!) (exprToSMT e `FpEqSMT` zero)]
funcToSMT1Prim IsNaN e = IsNaNSMT (exprToSMT e)
funcToSMT1Prim IsInfinite e = IsInfiniteSMT (exprToSMT e)
funcToSMT1Prim Abs e = AbsSMT (exprToSMT e)
funcToSMT1Prim Sqrt e = SqrtSMT (exprToSMT e)
funcToSMT1Prim Not e = (:!) (exprToSMT e)
funcToSMT1Prim (IntToFP ex s) e = IntToFPSMT ex s (exprToSMT e)
funcToSMT1Prim (FPToFP ex s) e = FPToFPSMT ex s (exprToSMT e)
funcToSMT1Prim IntToRational e = IntToRealSMT (exprToSMT e)
funcToSMT1Prim IntToString e = FromInt (exprToSMT e)
funcToSMT1Prim (BVToInt w) e = (BVToIntSMT w) (exprToSMT e)
funcToSMT1Prim (IntToBV w) e = (IntToBVSMT w) (exprToSMT e)
funcToSMT1Prim RationalToFloat e = RealToFloat (exprToSMT e)
funcToSMT1Prim RationalToDouble e = RealToDouble (exprToSMT e)
funcToSMT1Prim BVToNat e = BVToNatSMT (exprToSMT e)
funcToSMT1Prim Chr e = FromCode (exprToSMT e)
funcToSMT1Prim OrdChar e = ToCode (exprToSMT e)
funcToSMT1Prim StrLen e = StrLenSMT (exprToSMT e)

funcToSMT1Prim ForAllPr (Lam _ (Id n t) e) = ForAll (nameToStr n) (typeToSMT t) (exprToSMT e)

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
funcToSMT2Prim Minus a1 a2
    | typeOf a1 == TyLitWord =
        let
            bind1 = "INTERNAL_!!_Minus_1"
            bind2 = "INTERNAL_!!_Minus_2"

            v1 = V bind1 SortWord
            v2 = V bind2 SortWord

            mws = VWord maxBound
        in
          SLet (bind1, exprToSMT a1)
        . SLet (bind2, exprToSMT a2)
        $ IteSMT (v1 :>= v2) (v1 :- v2) (mws :- ((v2 `Modulo` mws) :- v1 :- VWord 1))
    | otherwise = exprToSMT a1 :- exprToSMT a2
funcToSMT2Prim Mult a1 a2 = exprToSMT a1 :* exprToSMT a2
funcToSMT2Prim Div a1 a2 = exprToSMT a1 :/ exprToSMT a2
funcToSMT2Prim Exp a1 a2 = exprToSMT a1 :^ exprToSMT a2

funcToSMT2Prim AddBV a1 a2 = exprToSMT a1 `BVAdd` exprToSMT a2
funcToSMT2Prim MinusBV a1 a2 = exprToSMT a1 `BVAdd` BVNeg (exprToSMT a2)
funcToSMT2Prim MultBV a1 a2 = exprToSMT a1 `BVMult` exprToSMT a2
funcToSMT2Prim ConcatBV a1 a2 = exprToSMT a1 `Concat` exprToSMT a2
funcToSMT2Prim ShiftLBV a1 a2 = exprToSMT a1 `ShiftL` exprToSMT a2
funcToSMT2Prim ShiftRBV a1 a2 = exprToSMT a1 `ShiftR` exprToSMT a2

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
funcToSMT2Prim RationalToFloat a1 a2  = exprToSMT a1 :/ exprToSMT a2
funcToSMT2Prim RationalToDouble a1 a2  = exprToSMT a1 :/ exprToSMT a2

funcToSMT2Prim StrGe a1 a2 = exprToSMT a1 `StrGeSMT` exprToSMT a2
funcToSMT2Prim StrGt a1 a2 = exprToSMT a1 `StrGtSMT` exprToSMT a2
funcToSMT2Prim StrLt a1 a2 = exprToSMT a1 `StrLtSMT` exprToSMT a2
funcToSMT2Prim StrLe a1 a2 = exprToSMT a1 `StrLeSMT` exprToSMT a2
funcToSMT2Prim StrAppend a1 a2  = exprToSMT a1 :++ exprToSMT a2
funcToSMT2Prim StrAt a1 a2 = exprToSMT a1 :!! exprToSMT a2
funcToSMT2Prim StrPrefixOf a1 a2  = StrPrefixOfSMT (exprToSMT a1) (exprToSMT a2)
funcToSMT2Prim StrSuffixOf a1 a2  = StrSuffixOfSMT (exprToSMT a1) (exprToSMT a2)
funcToSMT2Prim op lhs rhs = error $ "funcToSMT2Prim: invalid case with (op, lhs, rhs): " ++ show (op, lhs, rhs)

funcToSMT3Prim :: Primitive -> Expr -> Expr -> Expr -> SMTAST
funcToSMT3Prim Fp x y z = FpSMT  (exprToSMT x) (exprToSMT y) (exprToSMT z)
funcToSMT3Prim Ite x y z = IteSMT (exprToSMT x) (exprToSMT y) (exprToSMT z)
funcToSMT3Prim StrSubstr x y z = StrSubstrSMT (exprToSMT x) (exprToSMT y) (exprToSMT z)
funcToSMT3Prim StrIndexOf x y z = StrIndexOfSMT (exprToSMT x) (exprToSMT y) (exprToSMT z)
funcToSMT3Prim StrReplace x y z = StrReplaceSMT (exprToSMT x) (exprToSMT y) (exprToSMT z)
funcToSMT3Prim op _ _ _ = error $ "funcToSMT3Prim: invalid case with " ++ show op

altToSMT :: Lit -> Expr -> SMTAST
altToSMT (LitInt i) _ = VInt i
altToSMT (LitWord i) _ = VWord i
altToSMT (LitFloat f) _ = VFloat f
altToSMT (LitDouble d) _ = VDouble d
altToSMT (LitChar c) _ = VChar c
altToSMT am _ = error $ "Unhandled " ++ show am

createUniqVarDecls :: [(Name, Sort)] -> [SMTHeader]
createUniqVarDecls [] = []
createUniqVarDecls ((n,SortWord):xs) =
    let
        posAssert = Assert $ (V (nameToStr n) SortChar) :> VWord 0
    in
    VarDecl (nameToBuilder n) SortWord:posAssert:createUniqVarDecls xs
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
typeToSMT (TyFun (TyLitFP e s) _) = SortFP e s -- TODO: Remove this
typeToSMT TyLitInt = SortInt
typeToSMT TyLitWord = SortWord
typeToSMT (TyLitFP e s) = SortFP e s
typeToSMT TyLitRational = SortReal
typeToSMT (TyLitBV w) = SortBV w
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
toSolverAST (x :^ y) = function2 "^" (toSolverAST x) (toSolverAST y)
toSolverAST (x `QuotSMT` y) = function2 "div" (toSolverAST x) (toSolverAST y)
toSolverAST (x `Modulo` y) = function2 "mod" (toSolverAST x) (toSolverAST y)
toSolverAST (AbsSMT x) = "(abs " <> toSolverAST x <> ")"
toSolverAST (SqrtSMT x) = "(^ " <> toSolverAST x <> " 0.5)"
toSolverAST (Neg x) = function1 "-" $ toSolverAST x

toSolverAST (x `BVAdd` y) = function2 "bvadd" (toSolverAST x) (toSolverAST y)
toSolverAST (BVNeg x) = function1 "bvneg" (toSolverAST x)
toSolverAST (x `BVMult` y) = function2 "bvmul" (toSolverAST x) (toSolverAST y)
toSolverAST (x `Concat` y) = function2 "concat" (toSolverAST x) (toSolverAST y)
toSolverAST (x `ShiftL` y) = function2 "bvshl" (toSolverAST x) (toSolverAST y)
toSolverAST (x `ShiftR` y) = function2 "bvlshr" (toSolverAST x) (toSolverAST y)

toSolverAST (FpSMT x y z) = function3 "fp" (toSolverAST x) (toSolverAST y) (toSolverAST z)
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

toSolverAST (FpIsZero x) = function1 "fp.isZero" (toSolverAST x)
toSolverAST (FpIsNegative x) = function1 "fp.isNegative" (toSolverAST x)

toSolverAST (FpSqrtSMT x) = function2 "fp.sqrt" "RNE" (toSolverAST x)
toSolverAST (TruncZeroSMT x) = function2 "fp.roundToIntegral" "RTZ" (toSolverAST x)

toSolverAST (IsNormalSMT x) = function1 "fp.isNormal" (toSolverAST x)
toSolverAST (IsNaNSMT x) = function1 "fp.isNaN" (toSolverAST x)
toSolverAST (IsInfiniteSMT x) = function1 "fp.isInfinite" (toSolverAST x)

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

-- Note: arguments flipped because SMTLIB does not have str.>= or str.>
toSolverAST (StrGeSMT x y) = function2 "str.<=" (toSolverAST y) (toSolverAST x)
toSolverAST (StrGtSMT x y) = function2 "str.<" (toSolverAST y) (toSolverAST x)

toSolverAST (StrLtSMT x y) = function2 "str.<" (toSolverAST x) (toSolverAST y)
toSolverAST (StrLeSMT x y) = function2 "str.<=" (toSolverAST x) (toSolverAST y)

toSolverAST (x :++ y) = function2 "str.++" (toSolverAST x) (toSolverAST y)
toSolverAST (FromInt x) = function1 "str.from_int" $ toSolverAST x
toSolverAST (StrLenSMT x) = function1 "str.len" $ toSolverAST x
toSolverAST (x :!! y) = function2 "str.at" (toSolverAST x) (toSolverAST y)
toSolverAST (StrSubstrSMT x y z) = function3 "str.substr" (toSolverAST x) (toSolverAST y) (toSolverAST z)
toSolverAST (StrIndexOfSMT x y z) = function3 "str.indexof" (toSolverAST x) (toSolverAST y) (toSolverAST z)
toSolverAST (StrReplaceSMT x y z) = function3 "str.replace" (toSolverAST x) (toSolverAST y) (toSolverAST z)
toSolverAST (StrPrefixOfSMT x y) = function2 "str.prefixof" (toSolverAST x) (toSolverAST y)
toSolverAST (StrSuffixOfSMT x y) = function2 "str.suffixof" (toSolverAST x) (toSolverAST y)

toSolverAST (IntToRealSMT x) = function1 "to_real" $ toSolverAST x
toSolverAST (IntToFPSMT e s x) =
    function2 ("(_ to_fp " <> showText e <> " " <> showText s <> ")") "RNE" . function1 ("(_ int2bv " <> showText (e + s) <> ")") $ toSolverAST x
toSolverAST (FPToFPSMT e s x) = function2 ("(_ to_fp " <> showText e <> " " <> showText s <> ")") "RNE" $ toSolverAST x

toSolverAST (RealToFloat x) = function2 "(_ to_fp 8 24)" "RNE" (function1 "(_ int2bv 32)" $ toSolverAST x)
toSolverAST (RealToDouble x) = function2 "(_ to_fp 11 53)" "RNE" (function1 "(_ int2bv 64)" $ toSolverAST x)

toSolverAST (FloatToIntSMT x) = bvToSignedInt 32 (function2 "(_ fp.to_sbv 32)" "RNE" $ toSolverAST x)
toSolverAST (DoubleToIntSMT x) = bvToSignedInt 64 (function2 "(_ fp.to_sbv 64)" "RNE" $ toSolverAST x)
toSolverAST (BVToNatSMT x) = function1 "bv2nat" (toSolverAST x)
toSolverAST (BVToIntSMT w x) = bvToSignedInt w (toSolverAST x)
toSolverAST (IntToBVSMT w x) = function1 ("(_ int2bv " <> showText w <> ")") (toSolverAST x)

toSolverAST (IteSMT x y z) =
    function3 "ite" (toSolverAST x) (toSolverAST y) (toSolverAST z)

toSolverAST (SLet (n, e) body_e) =
    "(let ((" <> TB.string n <> " " <> toSolverAST e <> "))" <> toSolverAST body_e <> ")"

toSolverAST (FromCode chr) = function1 "str.from_code" (toSolverAST chr)
toSolverAST (ToCode chr) = function1 "str.to_code" (toSolverAST chr)

toSolverAST (VInt i) = if i >= 0 then showText i else "(- " <> showText (abs i) <> ")"
toSolverAST (VWord w) = showText w
toSolverAST (VFloat f) = convertFloating castFloatToWord32 8 f
toSolverAST (VDouble d) = convertFloating castDoubleToWord64 11 d
toSolverAST (VReal r) = "(/ " <> showText (numerator r) <> " " <> showText (denominator r) <> ")"
toSolverAST (VBitVec b) = "#b" <> foldr (<>) "" (map showText b)
toSolverAST (VString s) = "\"" <> TB.string s <> "\""
toSolverAST (VChar '"') = "\"\"\"\""
toSolverAST (VChar c) = "\"" <> TB.string [c] <> "\""
toSolverAST (VBool b) = if b then "true" else "false"
toSolverAST (V n _) = TB.string n

toSolverAST (Named x n) = "(! " <> toSolverAST x <> " :named " <> TB.string n <> ")"

toSolverAST (ForAll n srt smt) = "(forall ((" <> TB.string n <> " " <> sortName srt <> "))" <> toSolverAST smt <> ")"

-- | Converts a bit vector to a signed Int.
-- Z3 has a bv2int function, but uses unsigned integers.
-- The bit vector theory:
--      https://smt-lib.org/theories-FixedSizeBitVectors.shtml
-- has a note about converting bit vectors to signed ints:
--   "bv2int, which takes a bitvector b: [0, m) → {0, 1}
--    with 0 < m, and returns an integer in the range [- 2^(m - 1), 2^(m - 1)),
--    and is defined as follows:
--        bv2int(b) := if b(m-1) = 0 then bv2nat(b) else bv2nat(b) - 2^m"
bvToSignedInt :: Int -- ^ Bitvector width
              -> TB.Builder -- ^ Bitvector SMT expression
              -> TB.Builder
bvToSignedInt w smt =
    let
        ext = showText (w - 1)
    in
    function3 "ite" (function2 "=" (function1 ("(_ extract " <> ext <> " " <> ext <> ")") smt) "#b0")
                    (function1 "bv2nat" smt)
                    (function2 "-" (function1 "bv2nat" smt) (showText (2^w :: Integer)))

convertFloating :: (Num b, Bits.FiniteBits b) => (a -> b) -> Int -> a -> TB.Builder
convertFloating conv eb_width f =
    let
        w32 = convertBits $ conv f
        h:_ = w32
        eb = take eb_width $ drop 1 w32
        sb = drop (eb_width + 1) w32
    in
    "(fp #b" <> TB.char h <> " #b" <> TB.string eb <> " #b" <> TB.string sb <> ")"

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
sortName SortWord = "Int"
sortName SortFloat = "Float32"
sortName SortDouble = "Float64"
sortName (SortFP e s) = "(_ FloatingPoint " <> showText e <> " " <> showText s <> ")"
sortName SortReal = "Real"
sortName (SortBV w) = "(_ BitVec " <> showText w <> ")"
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
            QF_S -> "QF_S"
            _ -> "ALL"
    in
    "(set-logic " <> s <> ")"

-- | Converts an `SMTAST` to an `Expr`.
smtastToExpr :: KnownValues -> TypeEnv -> SMTAST -> Expr
smtastToExpr _ _ (VInt i) = Lit $ LitInt i
smtastToExpr _ _ (VWord i) = Lit $ LitWord i
smtastToExpr _ _ (VFloat f) = Lit $ LitFloat f
smtastToExpr _ _ (VDouble d) = Lit $ LitDouble d
smtastToExpr _ _ (VReal r) = Lit $ LitRational r
smtastToExpr _ _ (VBitVec bv) = Lit $ LitBV bv
smtastToExpr kv _ (VBool True) = mkTrue kv
smtastToExpr kv _ (VBool False) = mkFalse kv
smtastToExpr kv tenv (VString cs) = mkG2List kv tenv (tyChar kv) $ map (App (mkDCChar kv tenv) . Lit . LitChar) cs
smtastToExpr _ _ (VChar c) = Lit $ LitChar c
smtastToExpr _ _ (V n s) = Var $ Id (certainStrToName n) (sortToType s)
smtastToExpr _ _ _ = error "Conversion of this SMTAST to an Expr not supported."

-- | Converts a `Sort` to an `Type`.
sortToType :: Sort -> Type
sortToType SortInt = TyLitInt
sortToType SortWord = TyLitWord
sortToType SortFloat = TyLitFloat
sortToType SortDouble = TyLitDouble
sortToType SortReal = TyLitRational
sortToType SortChar = TyLitChar
sortToType SortBool = TyCon (Name "Bool" Nothing 0 Nothing) TYPE
sortToType _ = error "Conversion of this Sort to a Type not supported."

-- | Coverts an `SMTModel` to a `Model`.
modelAsExpr :: KnownValues -> TypeEnv ->SMTModel -> Model
modelAsExpr kv tenv = HM.fromList . M.toList . M.mapKeys strToName . M.map (smtastToExpr kv tenv)

certainStrToName :: String -> Name
certainStrToName s =
    case maybe_StrToName s of
        Just n -> n
        Nothing -> Name (T.pack s) Nothing 0 Nothing
