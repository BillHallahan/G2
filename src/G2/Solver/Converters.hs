{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings, RankNTypes, UndecidableInstances #-}

-- | This contains functions to switch from
-- (1) A State/Exprs/Types to SMTHeaders/SMTASTs/Sorts
-- (2) SMTHeaders/SMTASTs/Sorts to some SMT solver interface
-- (3) SMTASTs/Sorts to Exprs/Types
module G2.Solver.Converters
    ( PrintSMT
    , toSMTHeaders
    , toSolverText
    , toSolverASTString
    , toSolverASTSeq

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
import Data.Char
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid hiding (Alt)
import Data.Ratio
import qualified Data.Text as T
import GHC.Float
import qualified Text.Builder as TB
import Numeric

import qualified System.IO as IO
import System.Process

import G2.Language hiding (Assert, vars)
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC
import G2.Solver.Language
import G2.Solver.Solver
import qualified G2.Language.TyVarEnv as TV

type PrintSMT = Bool

-- | Used to describe the specific output format required by various solvers
-- By defining these functions, we can automatically convert from the SMTHeader and SMTAST
-- datatypes, to a form understandable by the solver.
class Solver con => SMTConverter con where
    getIO :: con -> (IO.Handle, IO.Handle, ProcessHandle)
    getPrintSMT :: con -> PrintSMT

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

checkConstraintsPC :: SMTConverter con => TV.TyVarEnv -> con -> PathConds -> IO (Result () () ())
checkConstraintsPC tv con pc = do
    let headers = toSMTHeaders tv pc
    checkConstraints con headers

checkConstraints :: SMTConverter con => con -> [SMTHeader] -> IO (Result () () ())
checkConstraints = checkSat

-- | Checks if the constraints are satisfiable, and returns a model if they are
checkModelPC :: SMTConverter con => ArbValueFunc -> con -> State t -> Bindings -> [Id] -> PathConds -> IO (Result SatRes () ())
checkModelPC avf con s b is pc = return . liftCasts (tyvar_env s) =<< checkModel' avf con s b is pc

-- | We split based on whether we are evaluating a ADT or a literal.
-- ADTs can be solved using our efficient addADTs, while literals require
-- calling an SMT solver.
checkModel' :: SMTConverter con => ArbValueFunc -> con -> State t -> Bindings -> [Id] -> PathConds -> IO (Result SatRes () ())
checkModel' _ _ s b [] _ = do
    return . SAT $ SatRes (model s) (tyvar_env s) (name_gen b)
checkModel' avf con s b (i:is) pc
    | (idName i) `HM.member` (model s) = checkModel' avf con s b is pc
    | otherwise =  do
        (m, av) <- getModelVal avf con s b i pc
        case m of
            SAT (SatRes m' tv_env ng) ->
                checkModel' avf con (s {tyvar_env = tv_env, model = HM.union m' (model s)}) (b {name_gen = ng, arb_value_gen = av}) is pc
            r -> return r

getModelVal :: SMTConverter con => ArbValueFunc -> con -> State t -> Bindings -> Id -> PathConds -> IO (Result SatRes () (), ArbValueGen)
getModelVal avf con s@(State { expr_env = eenv, type_env = tenv, known_values = kv, tyvar_env = tvnv }) b (Id n _) pc = do
    let (Just (Var (Id n' t))) = E.lookup n eenv
     
    case PC.null pc of
                True -> 
                    let
                        (e, tv_env', av, ng') = avf s (name_gen b) t (arb_value_gen b)
                    in
                    return (SAT $ SatRes (HM.singleton n' e) tv_env' ng', av) 
                False -> do
                    m <- solveNumericConstraintsPC tvnv con kv tenv pc (name_gen b)
                    return (m, arb_value_gen b)

solveNumericConstraintsPC :: SMTConverter con => TV.TyVarEnv -> con -> KnownValues -> TypeEnv -> PathConds -> NameGen -> IO (Result SatRes () ())
solveNumericConstraintsPC tv con kv tenv pc ng = do
    let headers = toSMTHeaders tv pc
    let vs = map (\(n', srt) -> (nameToStr n', srt)) . HS.toList . pcVars tv $ pc

    m <- solveConstraints con headers vs
    case m of
        SAT m' -> return . SAT $ SatRes (modelAsExpr kv tenv m') tv ng
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
toSMTHeaders :: TV.TyVarEnv -> PathConds -> [SMTHeader]
toSMTHeaders tv pc = addSetLogic  (toSMTHeaders' tv pc)

toSMTHeaders' :: TV.TyVarEnv -> PathConds -> [SMTHeader]
toSMTHeaders' tv pc  =
    let
        pc' = PC.toList pc
    in 
    (pcVarDecls tv pc)
    ++
    (pathConsToSMTHeaders tv pc')

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
             if str then SetLogic QF_SLIA else SetLogic ALL
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
isStr' (StrAppendSMT _) = All True
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

pathConsToSMTHeaders :: TV.TyVarEnv -> [PathCond] -> [SMTHeader]
pathConsToSMTHeaders tv = map (pathConsToSMT tv)

pathConsToSMT :: TV.TyVarEnv -> PathCond -> SMTHeader
pathConsToSMT tv (MinimizePC e) = Minimize $ exprToSMT tv e
pathConsToSMT tv (SoftPC pc) = AssertSoft (pathConsToSMT' tv pc) Nothing
pathConsToSMT tv pc = Assert (pathConsToSMT' tv pc) 

pathConsToSMT' :: TV.TyVarEnv -> PathCond -> SMTAST
pathConsToSMT' tv (AltCond l e b) =
    let
        exprSMT = exprToSMT tv e
        altSMT = altToSMT l e
    in
    if b then exprSMT := altSMT else (:!) (exprSMT := altSMT) 
pathConsToSMT' tv (ExtCond e b) =
    let
        exprSMT = exprToSMT tv e
    in
    if b then exprSMT else (:!) exprSMT
pathConsToSMT' tv (AssumePC (Id n t) num pc) =
    let
        idSMT = V (nameToStr n) (typeToSMT tv t) -- exprToSMT (Var i)
        intSMT = VInt $ toInteger num -- exprToSMT (Lit (LitInt $ toInteger num))
        pcSMT = map ( pathConsToSMT' tv . PC.unhashedPC) $ HS.toList pc
    in
    (idSMT := intSMT) :=> SmtAnd pcSMT
pathConsToSMT' _ (MinimizePC _) = error "pathConsToSMT': unsupported nesting of MinimizePC."
pathConsToSMT' _ (SoftPC _) = error "pathConsToSMT': unsupported nesting of SoftPC."

exprToSMT :: TV.TyVarEnv -> Expr -> SMTAST
exprToSMT tv (Var (Id n t)) = V (nameToStr n) (typeToSMT tv t)
exprToSMT _ (Lit c) =
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
exprToSMT _ (Data (DataCon n (TyCon (Name "Bool" _ _ _) _ ) _ _)) =
    case nameOcc n of
        "True" -> VBool True
        "False" -> VBool False
        _ -> error "Invalid bool in exprToSMT"
exprToSMT tv (Data (DataCon n t _ _)) = V (nameToStr n) (typeToSMT tv t)
exprToSMT tv (App (Data (DataCon (Name "[]" _ _ _) _ _ _)) type_t)
    | Just (TyCon (Name "Char" _ _ _) _) <- TV.deepLookup tv type_t = VString ""
exprToSMT tv e | [ Data (DataCon (Name ":" _ _ _) _ _ _)
                 , type_t
                 , App _ e1
                 , e2] <- unApp e
               , Just (TyCon (Name "Char" _ _ _) _) <- TV.deepLookup tv type_t = 
                case e2 of
                    App (Data (DataCon (Name "[]" _ _ _) _ _ _)) type_t'
                        | Just (TyCon (Name "Char" _ _ _) _) <- TV.deepLookup tv type_t' -> exprToSMT tv e1
                    _ -> StrAppendSMT [exprToSMT tv e1, exprToSMT tv e2]
exprToSMT tv a@(App _ _) =
    let
        f = getFunc a
        ars = getArgs a
    in
    funcToSMT tv f ars
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
exprToSMT tv (Case bindee _ _ as)
    | m_ls <- map fromLitAlt as
    , all isJust m_ls
    , ((_, init_e):ls) <- catMaybes m_ls =
        let
            bindee' = exprToSMT tv bindee
        in
        foldr (\(i, e) -> IteSMT (bindee' := VInt i) (exprToSMT tv e)) (exprToSMT tv init_e) ls
    where
        fromLitAlt (Alt (LitAlt (LitInt i)) e) = Just (i, e)
        fromLitAlt _ = Nothing
exprToSMT tv (Tick _ e) = exprToSMT tv e

exprToSMT _ e = error $ "exprToSMT: unhandled Expr: " ++ show e

-- | We split based on whether the passed Expr is a function or known data constructor, or an unknown data constructor
funcToSMT :: TV.TyVarEnv -> Expr -> [Expr] -> SMTAST
funcToSMT tv (Prim p _) [a] = funcToSMT1Prim tv p a
funcToSMT tv (Prim p _) [a1, a2] = funcToSMT2Prim tv p a1 a2
funcToSMT tv (Prim p _) [a1, a2, a3] = funcToSMT3Prim tv p a1 a2 a3
funcToSMT _ e l = error ("Unrecognized " ++ show e ++ " with args " ++ show l ++ " in funcToSMT")

funcToSMT1Prim :: TV.TyVarEnv -> Primitive -> Expr -> SMTAST
funcToSMT1Prim tv Negate a = Neg (exprToSMT tv a)
funcToSMT1Prim tv FpNeg a = FpNegSMT (exprToSMT tv a)
funcToSMT1Prim tv FpSqrt e = FpSqrtSMT (exprToSMT tv e)
funcToSMT1Prim tv TruncZero e | typeOf tv e == TyLitFloat = FloatToIntSMT (TruncZeroSMT (exprToSMT tv e))
                           | typeOf tv e == TyLitDouble = DoubleToIntSMT (TruncZeroSMT (exprToSMT tv e))
funcToSMT1Prim tv DecimalPart e | typeOf tv e == TyLitFloat = exprToSMT tv e `FpSubSMT` TruncZeroSMT (exprToSMT tv e)
                             | typeOf tv e == TyLitDouble = exprToSMT tv e `FpSubSMT` TruncZeroSMT (exprToSMT tv e)
funcToSMT1Prim tv FpIsNegativeZero e =
    let
        nz = "INTERNAL_!!_IsNegZero"
        smt_srt = typeToSMT tv (typeOf tv e) 
    in
    SLet (nz, exprToSMT tv e) $ SmtAnd [FpIsNegative (V nz smt_srt), FpIsZero (V nz smt_srt)]
funcToSMT1Prim tv IsDenormalized e =
    let
        zero = case typeOf tv e of
                    TyLitFloat -> VFloat 0
                    TyLitDouble -> VDouble 0
                    _ -> error "funcToSMT1Prim: bad type passed to IsDenormalized"
    in
    SmtAnd [(:!) (IsNormalSMT (exprToSMT tv e)), (:!) (exprToSMT tv e `FpEqSMT` zero)]
funcToSMT1Prim tv IsNaN e = IsNaNSMT (exprToSMT tv e)
funcToSMT1Prim tv IsInfinite e = IsInfiniteSMT (exprToSMT tv e)
funcToSMT1Prim tv Abs e = AbsSMT (exprToSMT tv e)
funcToSMT1Prim tv Sqrt e = SqrtSMT (exprToSMT tv e)
funcToSMT1Prim tv Not e = (:!) (exprToSMT tv e)
funcToSMT1Prim tv (IntToFP ex s) e = IntToFPSMT ex s (exprToSMT tv e)
funcToSMT1Prim tv (FPToFP ex s) e = FPToFPSMT ex s (exprToSMT tv e)
funcToSMT1Prim tv IntToRational e = IntToRealSMT (exprToSMT tv e)
funcToSMT1Prim tv IntToString e = FromInt (exprToSMT tv e)
funcToSMT1Prim tv (BVToInt w) e = (BVToIntSMT w) (exprToSMT tv e)
funcToSMT1Prim tv (IntToBV w) e = (IntToBVSMT w) (exprToSMT tv e)
funcToSMT1Prim tv RationalToFloat e = RealToFloat (exprToSMT tv e)
funcToSMT1Prim tv RationalToDouble e = RealToDouble (exprToSMT tv e)
funcToSMT1Prim tv BVToNat e = BVToNatSMT (exprToSMT tv e)
funcToSMT1Prim tv Chr e = FromCode (exprToSMT tv e)
funcToSMT1Prim tv OrdChar e = ToCode (exprToSMT tv e)
funcToSMT1Prim tv StrLen e = StrLenSMT (exprToSMT tv e)
funcToSMT1Prim tv SeqUnit e = SeqUnitSMT (exprToSMT tv e)

funcToSMT1Prim _ err _ = error $ "funcToSMT1Prim: invalid Primitive " ++ show err


funcToSMT2Prim :: TV.TyVarEnv -> Primitive -> Expr -> Expr -> SMTAST
funcToSMT2Prim tv And a1 a2 = SmtAnd [exprToSMT tv a1, exprToSMT tv a2]
funcToSMT2Prim tv Or a1 a2 = SmtOr [exprToSMT tv a1, exprToSMT tv a2]
funcToSMT2Prim tv Implies a1 a2 = exprToSMT tv a1 :=> exprToSMT tv a2
funcToSMT2Prim tv Iff a1 a2 = exprToSMT tv a1 :<=> exprToSMT tv a2
funcToSMT2Prim tv Ge a1 a2 = exprToSMT tv a1 :>= exprToSMT tv a2
funcToSMT2Prim tv Gt a1 a2 = exprToSMT tv a1 :> exprToSMT tv a2
funcToSMT2Prim tv Eq a1 a2 = exprToSMT tv a1 := exprToSMT tv a2
funcToSMT2Prim tv Neq a1 a2 = exprToSMT tv a1 :/= exprToSMT tv a2
funcToSMT2Prim tv Lt a1 a2 = exprToSMT tv a1 :< exprToSMT tv a2
funcToSMT2Prim tv Le a1 a2 = exprToSMT tv a1 :<= exprToSMT tv a2
funcToSMT2Prim tv Plus a1 a2 = exprToSMT tv a1 :+ exprToSMT tv a2
funcToSMT2Prim tv Minus a1 a2
    | typeOf tv a1 == TyLitWord =
        let
            bind1 = "INTERNAL_!!_Minus_1"
            bind2 = "INTERNAL_!!_Minus_2"

            v1 = V bind1 SortWord
            v2 = V bind2 SortWord

            mws = VWord maxBound
        in
          SLet (bind1, exprToSMT tv a1)
        . SLet (bind2, exprToSMT tv a2)
        $ IteSMT (v1 :>= v2) (v1 :- v2) (mws :- ((v2 `Modulo` mws) :- v1 :- VWord 1))
    | otherwise = exprToSMT tv a1 :- exprToSMT tv a2
funcToSMT2Prim tv Mult a1 a2 = exprToSMT tv a1 :* exprToSMT tv a2
funcToSMT2Prim tv Div a1 a2 = exprToSMT tv a1 :/ exprToSMT tv a2
funcToSMT2Prim tv Exp a1 a2 = exprToSMT tv a1 :^ exprToSMT tv a2

funcToSMT2Prim tv AddBV a1 a2 = exprToSMT tv a1 `BVAdd` exprToSMT tv a2
funcToSMT2Prim tv MinusBV a1 a2 = exprToSMT tv a1 `BVAdd` BVNeg (exprToSMT tv a2)
funcToSMT2Prim tv MultBV a1 a2 = exprToSMT tv a1 `BVMult` exprToSMT tv a2
funcToSMT2Prim tv ConcatBV a1 a2 = exprToSMT tv a1 `Concat` exprToSMT tv a2
funcToSMT2Prim tv ShiftLBV a1 a2 = exprToSMT tv a1 `ShiftL` exprToSMT tv a2
funcToSMT2Prim tv ShiftRBV a1 a2 = exprToSMT tv a1 `ShiftR` exprToSMT tv a2

funcToSMT2Prim tv FpAdd a1 a2 = exprToSMT tv a1 `FpAddSMT` exprToSMT tv a2
funcToSMT2Prim tv FpSub a1 a2 = exprToSMT tv a1 `FpSubSMT` exprToSMT tv a2
funcToSMT2Prim tv FpMul a1 a2 = exprToSMT tv a1 `FpMulSMT` exprToSMT tv a2
funcToSMT2Prim tv FpDiv a1 a2 = exprToSMT tv a1 `FpDivSMT` exprToSMT tv a2

funcToSMT2Prim tv FpLeq a1 a2 = exprToSMT tv a1 `FpLeqSMT` exprToSMT tv a2
funcToSMT2Prim tv FpLt a1 a2 = exprToSMT tv a1 `FpLtSMT` exprToSMT tv a2
funcToSMT2Prim tv FpGeq a1 a2 = exprToSMT tv a1 `FpGeqSMT` exprToSMT tv a2
funcToSMT2Prim tv FpGt a1 a2 = exprToSMT tv a1 `FpGtSMT` exprToSMT tv a2
funcToSMT2Prim tv FpEq a1 a2 = exprToSMT tv a1 `FpEqSMT` exprToSMT tv a2
funcToSMT2Prim tv FpNeq a1 a2 = (:!) (exprToSMT tv a1 `FpEqSMT` exprToSMT tv a2)

funcToSMT2Prim tv Quot a1 a2 = exprToSMT tv a1 `QuotSMT` exprToSMT tv a2
funcToSMT2Prim tv Mod a1 a2 = exprToSMT tv a1 `Modulo` exprToSMT tv a2
funcToSMT2Prim tv Rem a1 a2 = exprToSMT tv a1 :- ((exprToSMT tv a1 `QuotSMT` exprToSMT tv a2) :* exprToSMT tv a2) -- TODO: more efficient encoding?
funcToSMT2Prim tv RationalToFloat a1 a2  = exprToSMT tv a1 :/ exprToSMT tv a2
funcToSMT2Prim tv RationalToDouble a1 a2  = exprToSMT tv a1 :/ exprToSMT tv a2

funcToSMT2Prim tv StrGe a1 a2 = exprToSMT tv a1 `StrGeSMT` exprToSMT tv a2
funcToSMT2Prim tv StrGt a1 a2 = exprToSMT tv a1 `StrGtSMT` exprToSMT tv a2
funcToSMT2Prim tv StrLt a1 a2 = exprToSMT tv a1 `StrLtSMT` exprToSMT tv a2
funcToSMT2Prim tv StrLe a1 a2 = exprToSMT tv a1 `StrLeSMT` exprToSMT tv a2
funcToSMT2Prim tv StrAppend a1 a2  = StrAppendSMT [exprToSMT tv a1, exprToSMT tv a2]
funcToSMT2Prim tv StrAt a1 a2 = exprToSMT tv a1 :!! exprToSMT tv a2
funcToSMT2Prim tv StrPrefixOf a1 a2  = StrPrefixOfSMT (exprToSMT tv a1) (exprToSMT tv a2)
funcToSMT2Prim tv StrSuffixOf a1 a2  = StrSuffixOfSMT (exprToSMT tv a1) (exprToSMT tv a2)
funcToSMT2Prim tv op lhs rhs = error $ "funcToSMT2Prim: invalid case with (tyvar_env, op, lhs, rhs): " ++ show (tv, op, lhs, rhs)

funcToSMT3Prim :: TV.TyVarEnv -> Primitive -> Expr -> Expr -> Expr -> SMTAST
funcToSMT3Prim tv Fp x y z = FpSMT  (exprToSMT tv x) (exprToSMT tv y) (exprToSMT tv z)
funcToSMT3Prim tv Ite x y z = IteSMT (exprToSMT tv x) (exprToSMT tv y) (exprToSMT tv z)
funcToSMT3Prim tv StrSubstr x y z = StrSubstrSMT (exprToSMT tv x) (exprToSMT tv y) (exprToSMT tv z)
funcToSMT3Prim tv StrIndexOf x y z = StrIndexOfSMT (exprToSMT tv x) (exprToSMT tv y) (exprToSMT tv z)
funcToSMT3Prim tv StrReplace x y z = StrReplaceSMT (exprToSMT tv x) (exprToSMT tv y) (exprToSMT tv z)

funcToSMT3Prim tv ForAllBoundPr lower upper e_body | (Lam _ (Id n t) e) <- stripAllTicks e_body =
    let
        lower_smt = exprToSMT tv lower
        upper_smt = exprToSMT tv upper
        e_smt = exprToSMT tv e

        n_smt = nameToStr n
        n_sort = typeToSMT tv t
        n_var = V n_smt n_sort

        cond = SmtAnd [lower_smt :<= n_var, n_var :< upper_smt]
    in
    ForAll n_smt n_sort (cond :=> e_smt)

funcToSMT3Prim _ op _ _ _ = error $ "funcToSMT3Prim: invalid case with " ++ show op

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

pcVarDecls :: TV.TyVarEnv -> PathConds -> [SMTHeader]
pcVarDecls tv = createUniqVarDecls . HS.toList . pcVars tv

-- Get's all variable required for a list of `PathCond` 
pcVars :: TV.TyVarEnv -> PathConds -> HS.HashSet (Name, Sort)
pcVars tv = HS.map (idToNameSort tv) . PC.allIds

idToNameSort :: TV.TyVarEnv -> Id -> (Name, Sort)
idToNameSort tv (Id n t) = (n, typeToSMT tv t)

typeToSMT :: TV.TyVarEnv -> Type -> Sort
typeToSMT _ (TyFun TyLitInt _) = SortInt -- TODO: Remove this
typeToSMT _ (TyFun (TyLitFP e s) _) = SortFP e s -- TODO: Remove this
typeToSMT _ TyLitInt = SortInt
typeToSMT _ TyLitWord = SortWord
typeToSMT _ (TyLitFP e s) = SortFP e s
typeToSMT _ TyLitRational = SortReal
typeToSMT _ (TyLitBV w) = SortBV w
typeToSMT _ TyLitChar = SortChar
typeToSMT _ (TyCon (Name "Bool" _ _ _) _) = SortBool
#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
typeToSMT _ (TyApp (TyCon (Name "List" _ _ _) _) (TyCon (Name "Char" _ _ _) _)) = SortString
typeToSMT tv (TyApp (TyCon (Name "List" _ _ _) _) (TyVar (Id n _)))
    | Just (TyCon (Name "Char" _ _ _) _) <- TV.deepLookupName tv n = SortString
typeToSMT tv (TyApp (TyCon (Name "List" _ _ _) _) t) = SortSeq (adtTypeToSMT tv t)
#else
typeToSMT _ (TyApp (TyCon (Name "[]" _ _ _) _) (TyCon (Name "Char" _ _ _) _)) = SortString
typeToSMT tv (TyApp (TyCon (Name "[]" _ _ _) _) (TyVar (Id n _)))
    | Just (TyCon (Name "Char" _ _ _) _) <- TV.deepLookupName tv n = SortString
typeToSMT tv (TyApp (TyCon (Name "[]" _ _ _) _) t) = SortSeq (adtTypeToSMT tv t)
#endif
typeToSMT tv t@(TyApp t1 (TyVar (Id n _))) = case TV.deepLookupName tv n of 
                                                Just t2 -> typeToSMT tv (TyApp t1 t2)
                                                Nothing -> error $ "typeToSMT: TyVarEnv can't find the type: " ++ show t 
typeToSMT tv t@(TyVar (Id n _ )) = case TV.deepLookupName tv n of 
                                        Just t1 -> typeToSMT tv t1
                                        Nothing -> error $ "typeToSMT: TyVarEnv can't find the type: " ++ show t 
typeToSMT _ t = error $ "Unsupported type in typeToSMT: " ++ show t

adtTypeToSMT :: TyVarEnv -> Type -> Sort
adtTypeToSMT _ (TyCon (Name "Int" _ _ _) _) = SortInt
adtTypeToSMT _ (TyCon (Name "Integer" _ _ _) _) = SortInt
adtTypeToSMT _ (TyCon (Name "Float" _ _ _) _) = SortFloat
adtTypeToSMT _ (TyCon (Name "Double" _ _ _) _) = SortDouble
adtTypeToSMT tv (TyVar (Id n _)) | Just t <- TV.deepLookupName tv n = adtTypeToSMT tv t
adtTypeToSMT _ t = error $ "Unsupported type in adtTypeToSMT: " ++ show t

comment :: String -> TB.Builder
comment s = "; " <> TB.string s

assertSoftSolver :: TB.Builder -> Maybe T.Text -> TB.Builder
assertSoftSolver ast Nothing = function1 "assert-soft" ast
assertSoftSolver ast (Just lab) = "(assert-soft " <> ast <> " :id " <> TB.text lab <> ")"

defineFun :: (SMTAST -> TB.Builder) -> String -> [(String, Sort)] -> Sort -> SMTAST -> TB.Builder
defineFun str_seq fn ars ret body =
    "(define-fun " <> (TB.string fn) <> " ("
        <> TB.intercalate " " (map (\(n, s) -> "(" <> TB.string n <> " " <> sortName s <> ")") ars) <> ")"
        <> " (" <> sortName ret <> ") " <> toSolverAST str_seq body <> ")"

declareFun :: String -> [Sort] -> Sort -> TB.Builder
declareFun fn ars ret =
    "(declare-fun " <> TB.string fn <> " ("
        <> TB.intercalate " " (map sortName ars) <> ")"
        <> " (" <> sortName ret <> "))"

toSolverText :: (SMTAST -> TB.Builder) -> [SMTHeader] -> TB.Builder
toSolverText str_seq = TB.intercalate "\n" . map go
    where
        go (Assert ast) = function1 "assert" $ toSolverAST str_seq ast
        go (AssertSoft ast lab) = assertSoftSolver (toSolverAST str_seq ast) lab
        go (Minimize ast) = function1 "minimize" $ toSolverAST str_seq ast
        go (DefineFun f ars ret body) = defineFun str_seq f ars ret body
        go (DeclareFun f ars ret) = declareFun f ars ret
        go (VarDecl n s) = toSolverVarDecl n s
        go (SetLogic lgc) = toSolverSetLogic lgc
        go (Comment c) = comment c

toSolverAST :: (SMTAST -> TB.Builder) -- ^ Handling of String/Seq primitives
            -> SMTAST
            -> TB.Builder
toSolverAST str_seq = go
    where
        go (x :>= y) = function2 ">=" (go x) (go y)
        go (x :> y) = function2 ">" (go x) (go y)
        go (x := y) = function2 "=" (go x) (go y)
        go (x :/= y) = function1 "not" $ function2 "=" (go x) (go y)
        go (x :< y) = function2 "<" (go x) (go y)
        go (x :<= y) = function2 "<=" (go x) (go y)

        go (SmtAnd []) = "true"
        go (SmtAnd [x]) = go x
        go (SmtAnd xs) = functionList "and" $ map (go) xs
        go (SmtOr []) = "false"
        go (SmtOr [x]) = go x
        go (SmtOr xs) =  functionList "or" $ map (go) xs

        go ((:!) x) = function1 "not" $ go x
        go (x :=> y) = function2 "=>" (go x) (go y)
        go (x :<=> y) = function2 "=" (go x) (go y)

        go (x :+ y) = function2 "+" (go x) (go y)
        go (x :- y) = function2 "-" (go x) (go y)
        go (x :* y) = function2 "*" (go x) (go y)
        go (x :/ y) = function2 "/" (go x) (go y)
        go (x :^ y) = function2 "^" (go x) (go y)
        go (x `QuotSMT` y) = function2 "div" (go x) (go y)
        go (x `Modulo` y) = function2 "mod" (go x) (go y)
        go (AbsSMT x) = "(abs " <> go x <> ")"
        go (SqrtSMT x) = "(^ " <> go x <> " 0.5)"
        go (Neg x) = function1 "-" $ go x

        go (x `BVAdd` y) = function2 "bvadd" (go x) (go y)
        go (BVNeg x) = function1 "bvneg" (go x)
        go (x `BVMult` y) = function2 "bvmul" (go x) (go y)
        go (x `Concat` y) = function2 "concat" (go x) (go y)
        go (x `ShiftL` y) = function2 "bvshl" (go x) (go y)
        go (x `ShiftR` y) = function2 "bvlshr" (go x) (go y)

        go (FpSMT x y z) = function3 "fp" (go x) (go y) (go z)
        go (FpNegSMT x) = function1 "fp.neg" (go x)
        go (FpAddSMT x y) = function3 "fp.add" "RNE" (go x) (go y)
        go (FpSubSMT x y) = function3 "fp.sub" "RNE" (go x) (go y)
        go (FpMulSMT x y) = function3 "fp.mul" "RNE" (go x) (go y)
        go (FpDivSMT x y) = function3 "fp.div" "RNE" (go x) (go y)

        go (FpLeqSMT x y) = function2 "fp.leq" (go x) (go y)
        go (FpLtSMT x y) = function2 "fp.lt" (go x) (go y)
        go (FpGeqSMT x y) = function2 "fp.geq" (go x) (go y)
        go (FpGtSMT x y) = function2 "fp.gt" (go x) (go y)
        go (FpEqSMT x y) = function2 "fp.eq" (go x) (go y)

        go (FpIsZero x) = function1 "fp.isZero" (go x)
        go (FpIsNegative x) = function1 "fp.isNegative" (go x)

        go (FpSqrtSMT x) = function2 "fp.sqrt" "RNE" (go x)
        go (TruncZeroSMT x) = function2 "fp.roundToIntegral" "RTZ" (go x)

        go (IsNormalSMT x) = function1 "fp.isNormal" (go x)
        go (IsNaNSMT x) = function1 "fp.isNaN" (go x)
        go (IsInfiniteSMT x) = function1 "fp.isInfinite" (go x)

        go (ArrayConst v indS valS) =
            let
                sort_arr = "(Array " <> sortName indS <> " " <> sortName valS <> ")"
            in
            "((as const " <> sort_arr <> ") " <> (go v) <> ")"

        go (ArraySelect arr ind) =
            function2 "select" (go arr) (go ind)

        go (ArrayStore arr ind val) =
            function3 "store" (go arr) (go ind) (go val)

        go (Func n xs) = smtFunc n $ map (go) xs


        go (IntToRealSMT x) = function1 "to_real" $ go x
        go (IntToFPSMT e s x) =
            function2 ("(_ to_fp " <> showText e <> " " <> showText s <> ")") "RNE" . function1 ("(_ int2bv " <> showText (e + s) <> ")") $ go x
        go (FPToFPSMT e s x) = function2 ("(_ to_fp " <> showText e <> " " <> showText s <> ")") "RNE" $ go x

        go (RealToFloat x) = function2 "(_ to_fp 8 24)" "RNE" (function1 "(_ int2bv 32)" $ go x)
        go (RealToDouble x) = function2 "(_ to_fp 11 53)" "RNE" (function1 "(_ int2bv 64)" $ go x)

        go (FloatToIntSMT x) = bvToSignedInt 32 (function2 "(_ fp.to_sbv 32)" "RNE" $ go x)
        go (DoubleToIntSMT x) = bvToSignedInt 64 (function2 "(_ fp.to_sbv 64)" "RNE" $ go x)
        go (BVToNatSMT x) = function1 "bv2nat" (go x)
        go (BVToIntSMT w x) = bvToSignedInt w (go x)
        go (IntToBVSMT w x) = function1 ("(_ int2bv " <> showText w <> ")") (go x)

        go (IteSMT x y z) =
            function3 "ite" (go x) (go y) (go z)

        go (SLet (n, e) body_e) =
            "(let ((" <> TB.string n <> " " <> go e <> "))" <> go body_e <> ")"

        -- Note: arguments flipped because SMTLIB does not have str.>= or str.>
        go (StrGeSMT x y) = function2 "str.<=" (go y) (go x)
        go (StrGtSMT x y) = function2 "str.<" (go y) (go x)

        go (StrLtSMT x y) = function2 "str.<" (go x) (go y)
        go (StrLeSMT x y) = function2 "str.<=" (go x) (go y)

        go (FromInt x) = function1 "str.from_int" $ go x
        go (FromCode chr) = function1 "str.from_code" (go chr)
        go (ToCode chr) = function1 "str.to_code" (go chr)

        go (VInt i) = if i >= 0 then showText i else "(- " <> showText (abs i) <> ")"
        go (VWord w) = showText w
        go (VFloat f) = convertFloating castFloatToWord32 8 f
        go (VDouble d) = convertFloating castDoubleToWord64 11 d
        go (VReal r) = "(/ " <> showText (numerator r) <> " " <> showText (denominator r) <> ")"
        go (VBitVec b) = "#b" <> foldr (<>) "" (map showText b)
        go (VString s) = "\"" <> TB.string s <> "\""
        go (VChar '"') = "\"\"\"\""
        go (VChar c) | isPrint c = "\"" <> TB.string [c] <> "\""
                            | otherwise = "\"\\u{" <> TB.string (showHex (fromEnum c) "") <> "}\""
        go (VBool b) = if b then "true" else "false"
        go (V n _) = TB.string n

        go (Named x n) = "(! " <> go x <> " :named " <> TB.string n <> ")"

        go (ForAll n srt smt) = "(forall ((" <> TB.string n <> " " <> sortName srt <> "))" <> go smt <> ")"

        go (SeqUnitSMT e) = "(seq.unit " <> go e <> ")"

        go pr = str_seq pr

toSolverASTString :: SMTAST -> TB.Builder
toSolverASTString = go
    where
        go (StrAppendSMT xs) = functionList "str.++" (map goBack xs)
        go (StrLenSMT x) = function1 "str.len" $ goBack x
        go (x :!! y) = function2 "str.at" (goBack x) (goBack y)
        go (StrSubstrSMT x y z) = function3 "str.substr" (goBack x) (goBack y) (goBack z)
        go (StrIndexOfSMT x y z) = function3 "str.indexof" (goBack x) (goBack y) (goBack z)
        go (StrReplaceSMT x y z) = function3 "str.replace" (goBack x) (goBack y) (goBack z)
        go (StrPrefixOfSMT x y) = function2 "str.prefixof" (goBack x) (goBack y)
        go (StrSuffixOfSMT x y) = function2 "str.suffixof" (goBack x) (goBack y)
        go _ = error "toSolverASTString: primitive not handled"

        goBack = toSolverAST toSolverASTString

toSolverASTSeq :: SMTAST -> TB.Builder
toSolverASTSeq = go
    where
        go (StrAppendSMT xs) = functionList "seq.++" (map goBack xs)
        go (StrLenSMT x) = function1 "seq.len" $ goBack x
        go (x :!! y) = function2 "seq.at" (goBack x) (goBack y)
        go (StrSubstrSMT x y z) = function3 "seq.extract" (goBack x) (goBack y) (goBack z)
        go (StrIndexOfSMT x y z) = function3 "seq.indexof" (goBack x) (goBack y) (goBack z)
        go (StrReplaceSMT x y z) = function3 "seq.replace" (goBack x) (goBack y) (goBack z)
        go (StrPrefixOfSMT x y) = function2 "seq.prefixof" (goBack x) (goBack y)
        go (StrSuffixOfSMT x y) = function2 "seq.suffixof" (goBack x) (goBack y)
        go _ = error "toSolverASTSeq: primitive not handled"

        goBack = toSolverAST toSolverASTSeq

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
sortName (SortSeq s) = "(Seq " <> sortName s <> ")"
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
            QF_SLIA -> "QF_SLIA"
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
smtastToExpr kv tenv SeqEmptySMT = App (mkEmpty kv tenv) (Type TyUnknown)
smtastToExpr kv tenv (SeqUnitSMT s) = mkApp [ mkCons kv tenv
                                            , Type TyUnknown
                                            , wrapDC kv tenv $ smtastToExpr kv tenv s
                                            , App (mkEmpty kv tenv) (Type TyUnknown) ]
smtastToExpr kv tenv (StrAppendSMT xs) = mkG2List kv tenv TyUnknown $ map (wrapDC kv tenv . smtastToExpr kv tenv . fromUnit) xs
    where
        fromUnit (SeqUnitSMT s) = s
        fromUnit _ = error "fromUnit: unsupported case"
smtastToExpr _ _ _ = error "Conversion of this SMTAST to an Expr not supported."


wrapDC :: KnownValues -> TypeEnv -> Expr -> Expr
wrapDC kv tenv i@(Lit (LitInt _)) = App (mkDCInt kv tenv) i
wrapDC kv tenv i@(Lit (LitFloat _)) = App (mkDCFloat kv tenv) i
wrapDC kv tenv i@(Lit (LitDouble _)) = App (mkDCDouble kv tenv) i
wrapDC _ _ e = e

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
