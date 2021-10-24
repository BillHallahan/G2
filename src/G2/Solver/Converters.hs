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
    , toSolver
    , exprToSMT --WOULD BE NICE NOT TO EXPORT THIS
    , typeToSMT --WOULD BE NICE NOT TO EXPORT THIS
    , toSolverAST --WOULD BE NICE NOT TO EXPORT THIS
    , sortName
    , smtastToExpr
    , modelAsExpr
    , checkConstraintsPC
    , checkModelPC
    , checkConstraints
    , solveConstraints
    , constraintsToModelOrUnsatCore
    , SMTConverter (..) ) where

import Data.List
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import qualified Data.Set as S
import qualified Data.Text as T

import G2.Language hiding (Assert, vars)
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC
import G2.Solver.Language
import G2.Solver.Solver

-- | Used to describe the specific output format required by various solvers
-- By defining these functions, we can automatically convert from the SMTHeader and SMTAST
-- datatypes, to a form understandable by the solver.
class Solver con => SMTConverter con ast out io | con -> ast, con -> out, con -> io where
    getIO :: con -> io
    closeIO :: con -> IO ()

    empty :: con -> out
    merge :: con -> out -> out -> out

    checkSat :: con -> io -> out -> IO (Result () ())
    checkSatGetModel :: con -> io -> out -> [(SMTName, Sort)] -> IO (Result SMTModel ())
    checkSatGetModelOrUnsatCore :: con -> io -> out -> [(SMTName, Sort)] -> IO (Result SMTModel UnsatCore)
    checkSatGetModelGetExpr :: con -> io -> out -> [SMTHeader] -> [(SMTName, Sort)] -> ExprEnv -> CurrExpr
                            -> IO (Result SMTModel (), Maybe Expr)

    assertSolver :: con -> ast -> out
    assertSoftSolver :: con -> ast -> Maybe T.Text -> out
    defineFun :: con -> SMTName -> [(SMTName, Sort)] -> Sort -> SMTAST -> out 
    declareFun :: con -> SMTName -> [Sort] -> Sort -> out 
    varDecl :: con -> SMTNameBldr -> ast -> out

    setLogic :: con -> Logic -> out

    comment :: con -> String -> out

    (.>=) :: con -> ast -> ast -> ast
    (.>) :: con -> ast -> ast -> ast
    (.=) :: con -> ast -> ast -> ast
    (./=) :: con -> ast -> ast -> ast
    (.<) :: con -> ast -> ast -> ast
    (.<=) :: con -> ast -> ast -> ast

    smtAnd :: con -> [ast] -> ast
    smtOr :: con -> [ast] -> ast
    (.!) :: con -> ast -> ast
    (.=>) :: con -> ast -> ast -> ast
    (.<=>) :: con -> ast -> ast -> ast

    (.+) :: con -> ast -> ast -> ast
    (.-) :: con -> ast -> ast -> ast
    (.*) :: con -> ast -> ast -> ast
    (./) :: con -> ast -> ast -> ast
    smtQuot :: con -> ast -> ast -> ast
    smtModulo :: con -> ast -> ast -> ast
    smtSqrt :: con -> ast -> ast
    neg :: con -> ast -> ast

    arrayStore :: con -> ast -> ast -> ast -> ast
    arraySelect :: con -> ast -> ast -> ast

    smtFunc :: con -> SMTName -> [ast] -> ast

    strLen :: con -> ast -> ast
    itor :: con -> ast -> ast

    ite :: con -> ast -> ast -> ast -> ast

    --values
    int :: con -> Integer -> ast
    float :: con -> Rational -> ast
    double :: con -> Rational -> ast
    char :: con -> Char -> ast
    bool :: con -> Bool -> ast
    constArray :: con
               -> ast -- ^ value to put in array
               -> ast -- ^ Index sort of array
               -> ast -- ^ Val sort of array
               -> ast
    cons :: con -> SMTName -> [ast] -> Sort -> ast
    var :: con -> SMTName -> ast -> ast

    --sorts
    sortInt :: con -> ast
    sortFloat :: con -> ast
    sortDouble :: con -> ast
    sortChar :: con -> ast
    sortBool :: con -> ast
    sortArray :: con -> ast -> ast -> ast

    varName :: con -> SMTName -> Sort -> ast

    -- unsat cores
    named :: con -> ast -> SMTName -> ast

checkConstraintsPC :: SMTConverter con ast out io => con -> PathConds -> IO (Result () ())
checkConstraintsPC con pc = do
    let pc' = unsafeElimCast pc

    let headers = toSMTHeaders $ PC.toList pc'
    checkConstraints con headers

checkConstraints :: SMTConverter con ast out io => con -> [SMTHeader] -> IO (Result () ())
checkConstraints con headers = do
    let formula = toSolver con headers

    checkSat con (getIO con) formula

-- | Checks if the constraints are satisfiable, and returns a model if they are
checkModelPC :: SMTConverter con ast out io => ArbValueFunc -> con -> State t -> Bindings -> [Id] -> PathConds -> IO (Result Model ())
checkModelPC avf con s b is pc = return . liftCasts =<< checkModel' avf con s b is pc

-- | We split based on whether we are evaluating a ADT or a literal.
-- ADTs can be solved using our efficient addADTs, while literals require
-- calling an SMT solver.
checkModel' :: SMTConverter con ast out io => ArbValueFunc -> con -> State t -> Bindings -> [Id] -> PathConds -> IO (Result Model ())
checkModel' _ _ s _ [] _ = do
    return (SAT $ model s)
checkModel' avf con s b (i:is) pc
    | (idName i) `HM.member` (model s) = checkModel' avf con s b is pc
    | otherwise =  do
        (m, av) <- getModelVal avf con s b i pc
        case m of
            Just m' -> checkModel' avf con (s {model = HM.union m' (model s)}) (b {arb_value_gen = av}) is pc
            Nothing -> return $ UNSAT ()

getModelVal :: SMTConverter con ast out io => ArbValueFunc -> con -> State t -> Bindings -> Id -> PathConds -> IO (Maybe Model, ArbValueGen)
getModelVal avf con s b (Id n _) pc = do
    let (Just (Var (Id n' t))) = E.lookup n (expr_env s)
     
    case PC.null pc of
                True -> 
                    let
                        (e, av) = avf t (type_env s) (arb_value_gen b)
                    in
                    return (Just $ HM.singleton n' e, av) 
                False -> do
                    m <- solveNumericConstraintsPC con pc
                    return (m, arb_value_gen b)

solveNumericConstraintsPC :: SMTConverter con ast out io => con -> PathConds -> IO (Maybe Model)
solveNumericConstraintsPC con pc = do
    let headers = toSMTHeaders $ PC.toList pc
    let vs = map (\(n', srt) -> (nameToStr n', srt)) . HS.toList . pcVars $ PC.toList pc

    m <- solveConstraints con headers vs
    return $ fmap modelAsExpr m

solveConstraints :: SMTConverter con ast out io => con -> [SMTHeader] -> [(SMTName, Sort)] -> IO (Maybe SMTModel)
solveConstraints con headers vs = do
    let io = getIO con
    let formula = toSolver con headers
    r <- checkSatGetModel con io formula vs

    case r of
        SAT m' -> return $ Just m'
        _ -> return Nothing

constraintsToModelOrUnsatCore :: SMTConverter con ast out io => con -> [SMTHeader] -> [(SMTName, Sort)] -> IO (Result SMTModel UnsatCore)
constraintsToModelOrUnsatCore con headers vs = do
    let io = getIO con
    let formula = toSolver con headers
    checkSatGetModelOrUnsatCore con io formula vs

-- | Here we convert from a State, to an SMTHeader.  This SMTHeader can later
-- be given to an SMT solver by using toSolver.
-- To determine the input that can be fed to a state to get the curr_expr,
-- we need only consider the types and path constraints of that state.
-- We can also pass in some other Expr Container to instantiate names from, which is
-- important if you wish to later be able to scrape variables from those Expr's
toSMTHeaders :: [PathCond] -> [SMTHeader]
toSMTHeaders = addSetLogic . toSMTHeaders'

toSMTHeaders' :: [PathCond] -> [SMTHeader]
toSMTHeaders' pc  = 
    (pcVarDecls pc)
    ++
    (pathConsToSMTHeaders pc)

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
isLRA' (VFloat _) = All True
isLRA' (VDouble _) = All True
isLRA' (V _ s) = All $ isRASort s
isLRA' s = isCore' s

isRASort :: Sort -> Bool
isRASort SortFloat = True
isRASort SortDouble = True
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
pathConsToSMTHeaders = map Assert . mapMaybe pathConsToSMT

pathConsToSMT :: PathCond -> Maybe SMTAST
pathConsToSMT (AltCond l e b) =
    let
        exprSMT = exprToSMT e
        altSMT = altToSMT l e
    in
    Just $ if b then exprSMT := altSMT else (:!) (exprSMT := altSMT) 
pathConsToSMT (ExtCond e b) =
    let
        exprSMT = exprToSMT e
    in
    Just $ if b then exprSMT else (:!) exprSMT
pathConsToSMT (AssumePC i num pc) =
    let
        idSMT = exprToSMT (Var i)
        intSMT = exprToSMT (Lit (LitInt $ toInteger num))
    in case pathConsToSMT $ PC.unhashedPC pc of
        (Just pcSMT) -> Just $ (idSMT := intSMT) :=> pcSMT
        Nothing -> error $ "Unable to convert pc: " ++ (show pc)

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
funcToSMT1Prim SqRt e = SqrtSMT (exprToSMT e)
funcToSMT1Prim Not e = (:!) (exprToSMT e)
funcToSMT1Prim IntToFloat e = ItoR (exprToSMT e)
funcToSMT1Prim IntToDouble e = ItoR (exprToSMT e)
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
funcToSMT2Prim Quot a1 a2 = exprToSMT a1 `QuotSMT` exprToSMT a2
funcToSMT2Prim Mod a1 a2 = exprToSMT a1 `Modulo` exprToSMT a2
funcToSMT2Prim Rem a1 a2 = exprToSMT a1 :- ((exprToSMT a1 `QuotSMT` exprToSMT a2) :* exprToSMT a2) -- TODO: more efficient encoding?
funcToSMT2Prim RationalToDouble a1 a2  = exprToSMT a1 :/ exprToSMT a2
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
        lenAssert = Assert $ StrLen (V (nameToStr n) SortChar) := VInt 1
    in
    VarDecl (nameToBuilder n) SortChar:lenAssert:createUniqVarDecls xs
createUniqVarDecls ((n,s):xs) = VarDecl (nameToBuilder n) s:createUniqVarDecls xs

pcVarDecls :: [PathCond] -> [SMTHeader]
pcVarDecls = createUniqVarDecls . HS.toList . pcVars

-- Get's all variable required for a list of `PathCond` 
pcVars :: [PathCond] -> HS.HashSet (Name, Sort)
pcVars = foldr HS.union HS.empty . map pcVar

pcVar :: PathCond -> HS.HashSet (Name, Sort)
pcVar (AssumePC i _ pc) = HS.insert (idToNameSort i) (pcVar (PC.unhashedPC pc))
pcVar (AltCond _ e _) = vars e
pcVar p = vars p

vars :: (ASTContainer m Expr) => m -> HS.HashSet (Name, Sort)
vars = evalASTs vars'
    where
        vars' :: Expr -> HS.HashSet (Name, Sort)
        vars' (Var i) = HS.singleton (idToNameSort i)
        vars' _ = HS.empty

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
typeToSMT (TyForAll (AnonTyBndr _) t) = typeToSMT t
typeToSMT t = error $ "Unsupported type in typeToSMT: " ++ show t

toSolver :: SMTConverter con ast out io => con -> [SMTHeader] -> out
toSolver con [] = empty con
toSolver con (Assert ast:xs) = 
    merge con (assertSolver con $ toSolverAST con ast) (toSolver con xs)
toSolver con (AssertSoft ast lab:xs) = 
    merge con (assertSoftSolver con (toSolverAST con ast) lab) (toSolver con xs)
toSolver con (DefineFun f ars ret body:xs) =
    merge con (defineFun con f ars ret body) (toSolver con xs)
toSolver con (DeclareFun f ars ret:xs) =
    merge con (declareFun con f ars ret) (toSolver con xs)
toSolver con (VarDecl n s:xs) = merge con (toSolverVarDecl con n s) (toSolver con xs)
toSolver con (SetLogic lgc:xs) = merge con (toSolverSetLogic con lgc) (toSolver con xs)
toSolver con (Comment c:xs) = merge con (comment con c) (toSolver con xs)

toSolverAST :: SMTConverter con ast out io => con -> SMTAST -> ast
toSolverAST con (x :>= y) = (.>=) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :> y) = (.>) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x := y) = (.=) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :/= y) = (./=) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :< y) = (.<) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :<= y) = (.<=) con (toSolverAST con x) (toSolverAST con y)

toSolverAST con (SmtAnd xs) = smtAnd con $ map (toSolverAST con) xs
toSolverAST con (SmtOr xs) =  smtOr con $ map (toSolverAST con) xs
toSolverAST con ((:!) x) = (.!) con $ toSolverAST con x
toSolverAST con (x :=> y) = (.=>) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :<=> y) = (.<=>) con (toSolverAST con x) (toSolverAST con y)

toSolverAST con (x :+ y) = (.+) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :- y) = (.-) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :* y) = (.*) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :/ y) = (./) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x `QuotSMT` y) = smtQuot con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x `Modulo` y) = smtModulo con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (SqrtSMT x) = smtSqrt con $ toSolverAST con x
toSolverAST con (Neg x) = neg con $ toSolverAST con x

toSolverAST con (ArrayConst v indS valS) =
    constArray con (toSolverAST con v) (sortName con indS) (sortName con valS)

toSolverAST con (ArraySelect arr ind) =
    arraySelect con (toSolverAST con arr) (toSolverAST con ind)

toSolverAST con (ArrayStore arr ind val) =
    arrayStore con (toSolverAST con arr) (toSolverAST con ind) (toSolverAST con val)

toSolverAST con (Func n xs) = smtFunc con n $ map (toSolverAST con) xs

toSolverAST con (StrLen x) = strLen con $ toSolverAST con x
toSolverAST con (ItoR x) = itor con $ toSolverAST con x

toSolverAST con (Ite x y z) =
    ite con (toSolverAST con x) (toSolverAST con y) (toSolverAST con z)

toSolverAST con (VInt i) = int con i
toSolverAST con (VFloat f) = float con f
toSolverAST con (VDouble i) = double con i
toSolverAST con (VChar c) = char con c
toSolverAST con (VBool b) = bool con b
toSolverAST con (V n s) = varName con n s

toSolverAST con (Named x n) = named con (toSolverAST con x) n

toSolverAST _ ast = error $ "toSolverAST: invalid SMTAST: " ++ show ast

toSolverVarDecl :: SMTConverter con ast out io => con -> SMTNameBldr -> Sort -> out
toSolverVarDecl con n s = varDecl con n (sortName con s)

sortName :: SMTConverter con ast out io => con -> Sort -> ast
sortName con SortInt = sortInt con
sortName con SortFloat = sortFloat con
sortName con SortDouble = sortDouble con
sortName con SortChar = sortChar con
sortName con SortBool = sortBool con
sortName con (SortArray ind val) = sortArray con (sortName con ind) (sortName con val)

toSolverSetLogic :: SMTConverter con ast out io => con -> Logic -> out
toSolverSetLogic = setLogic

-- | Converts an `SMTAST` to an `Expr`.
smtastToExpr :: SMTAST -> Expr
smtastToExpr (VInt i) = (Lit $ LitInt i)
smtastToExpr (VFloat f) = (Lit $ LitFloat f)
smtastToExpr (VDouble d) = (Lit $ LitDouble d)
smtastToExpr (VBool b) =
    Data (DataCon (Name (T.pack $ show b) Nothing 0 Nothing) (TyCon (Name "Bool" Nothing 0 Nothing) TYPE))
smtastToExpr (VChar c) = Lit $ LitChar c
smtastToExpr (V n s) = Var $ Id (certainStrToName n) (sortToType s)
smtastToExpr _ = error "Conversion of this SMTAST to an Expr not supported."

-- | Converts a `Sort` to an `Type`.
sortToType :: Sort -> Type
sortToType (SortInt) = TyLitInt
sortToType (SortFloat) = TyLitFloat
sortToType (SortDouble) = TyLitDouble
sortToType (SortChar) = TyLitChar
sortToType (SortBool) = TyCon (Name "Bool" Nothing 0 Nothing) TYPE

-- | Coverts an `SMTModel` to a `Model`.
modelAsExpr :: SMTModel -> Model
modelAsExpr = HM.fromList . M.toList . M.mapKeys strToName . M.map smtastToExpr

certainStrToName :: String -> Name
certainStrToName s =
    case maybe_StrToName s of
        Just n -> n
        Nothing -> Name (T.pack s) Nothing 0 Nothing
