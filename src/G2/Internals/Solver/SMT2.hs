-- | This defines an SMTConverter for the SMT2 language
-- It provides methods to construct formulas, as well as feed them to an external solver

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}

module G2.Internals.Solver.SMT2 where

import G2.Internals.Config.Config
import G2.Internals.Language.Expr
import G2.Internals.Language.Support hiding (Model)
import G2.Internals.Language.Syntax hiding (Assert)
import G2.Internals.Language.Typing
import G2.Internals.Solver.Language
import G2.Internals.Solver.ParseSMT
import G2.Internals.Solver.Converters --It would be nice to not import this...

import Control.Exception.Base (evaluate)
import Data.List
import Data.List.Utils (countElem)
import qualified Data.Map as M
import Data.Ratio
import System.IO
import System.Process

data Z3 = Z3
data CVC4 = CVC4

data SomeSMT io where
    SomeSMT :: forall con ast out io . SMTConverter con ast out io => con -> SomeSMT io

instance SMTConverter Z3 String String (Handle, Handle, ProcessHandle) where
    empty _ = ""  
    merge _ = (++)

    checkSat _ (h_in, h_out, _) formula = do
        -- putStrLn "checkSat"
        -- putStrLn formula
        
        setUpFormulaZ3 h_in formula
        r <- checkSat' h_in h_out

        -- putStrLn $ show r

        return r

    checkSatGetModel _ (h_in, h_out, _) formula headers vs = do
        setUpFormulaZ3 h_in formula
        -- putStrLn "\n\n checkSatGetModel"
        -- putStrLn formula
        r <- checkSat' h_in h_out
        -- putStrLn $ "r =  " ++ show r
        if r == SAT then do
            mdl <- getModelZ3 h_in h_out vs
            -- putStrLn "======"
            -- putStrLn (show mdl)
            let m = parseModel headers mdl
            -- putStrLn $ "m = " ++ show m
            -- putStrLn "======"
            return (r, Just m)
        else do
            return (r, Nothing)

    checkSatGetModelGetExpr con (h_in, h_out, _) formula headers vs eenv (CurrExpr _ e) = do
        setUpFormulaZ3 h_in formula
        -- putStrLn "\n\n checkSatGetModelGetExpr"
        -- putStrLn formula
        r <- checkSat' h_in h_out
        -- putStrLn $ "r =  " ++ show r
        if r == SAT then do
            mdl <- getModelZ3 h_in h_out vs
            -- putStrLn "======"
            -- putStrLn formula
            -- putStrLn ""
            -- putStrLn (show mdl)
            -- putStrLn "======"
            let m = parseModel headers mdl

            expr <- solveExpr h_in h_out con headers eenv e
            -- putStrLn (show expr)
            return (r, Just m, Just expr)
        else do
            return (r, Nothing, Nothing)

    assert _ = function1 "assert"
        
    varDecl _ n s = "(declare-const " ++ n ++ " " ++ s ++ ")"
    
    setLogic _ lgc =
        let 
            s = case lgc of
                QF_LIA -> "QF_LIA"
                QF_LRA -> "QF_LRA"
                QF_LIRA -> "QF_LIRA"
                QF_NIA -> "QF_NIA"
                QF_NRA -> "QF_NRA"
                QF_NIRA -> "QF_NIRA"
                _ -> "ALL"
        in
        case lgc of
            ALL -> ""
            _ -> "(set-logic " ++ s ++ ")"

    (.>=) _ = function2 ">="
    (.>) _ = function2 ">"
    (.=) _ = function2 "="
    (./=) _ x = function1 "not" . function2 "=" x
    (.<=) _ = function2 "<="
    (.<) _ = function2 "<"

    (.&&) _ = function2 "and"
    (.||) _ = function2 "or"
    (.!) _ = function1 "not"
    (.=>) _ = function2 "=>"
    (.<=>) _ = function2 "="

    (.+) _ = function2 "+"
    (.-) _ = function2 "-"
    (.*) _ = function2 "*"
    (./) _ = function2 "/"
    smtQuot _ = function2 "div"
    smtModulo _ = function2 "mod"
    smtSqrt _ x = "(^ " ++ x ++ " 0.5)" 
    neg _ = function1 "-"

    itor _ = function1 "to_real"


    ite _ = function3 "ite"

    int _ x = if x >= 0 then show x else "(- " ++ show (abs x) ++ ")"
    float _ r = 
        "(/ " ++ show (numerator r) ++ " " ++ show (denominator r) ++ ")"
    double _ r =
        "(/ " ++ show (numerator r) ++ " " ++ show (denominator r) ++ ")"
    bool _ b = if b then "true" else "false"
    var _ n = function1 n

    sortInt _ = "Int"
    sortFloat _ = "Real"
    sortDouble _ = "Real"
    sortBool _ = "Bool"

    cons _ n asts _ =
        if asts /= [] then
            "(" ++ n ++ " " ++ (intercalate " " asts) ++ ")" 
        else
            n
    varName _ n _ = n

instance SMTConverter CVC4 String String (Handle, Handle, ProcessHandle) where
    empty _ = ""  
    merge _ = (++)

    checkSat _ (h_in, h_out, _) formula = do
        -- putStrLn "checkSat"
        -- putStrLn formula
        
        setUpFormulaCVC4 h_in formula
        r <- checkSat' h_in h_out

        -- putStrLn $ show r

        return r

    checkSatGetModel _ (h_in, h_out, _) formula headers vs = do
        setUpFormulaCVC4 h_in formula
        -- putStrLn "\n\n checkSatGetModel"
        -- putStrLn formula
        r <- checkSat' h_in h_out
        -- putStrLn $ "r =  " ++ show r
        if r == SAT then do
            mdl <- getModelCVC4 h_in h_out vs
            -- putStrLn "======"
            -- putStrLn (show mdl)
            let m = parseModel headers mdl
            -- putStrLn $ "m = " ++ show m
            -- putStrLn "======"
            return (r, Just m)
        else do
            return (r, Nothing)

    checkSatGetModelGetExpr con (h_in, h_out, _) formula headers vs eenv (CurrExpr _ e) = do
        setUpFormulaCVC4 h_in formula
        -- putStrLn "\n\n checkSatGetModelGetExpr"
        -- putStrLn formula
        r <- checkSat' h_in h_out
        -- putStrLn $ "r =  " ++ show r
        if r == SAT then do
            mdl <- getModelCVC4 h_in h_out vs
            -- putStrLn "======"
            -- putStrLn formula
            -- putStrLn ""
            -- putStrLn (show mdl)
            -- putStrLn "======"
            let m = parseModel headers mdl

            expr <- solveExpr h_in h_out con headers eenv e
            -- putStrLn (show expr)
            return (r, Just m, Just expr)
        else do
            return (r, Nothing, Nothing)

    assert _ = function1 "assert"
        
    varDecl _ n s = "(declare-const " ++ n ++ " " ++ s ++ ")"
    
    setLogic _ lgc =
        let 
            s = case lgc of
                QF_LIA -> "QF_LIA"
                QF_LRA -> "QF_LRA"
                QF_LIRA -> "QF_LIRA"
                QF_NIA -> "QF_NIA"
                QF_NRA -> "QF_NRA"
                QF_NIRA -> "QF_NIRA"
                _ -> "ALL"
        in
        case lgc of
            ALL -> ""
            _ -> "(set-logic " ++ s ++ ")"

    (.>=) _ = function2 ">="
    (.>) _ = function2 ">"
    (.=) _ = function2 "="
    (./=) _ = \x -> function1 "not" . function2 "=" x
    (.<=) _ = function2 "<="
    (.<) _ = function2 "<"

    (.&&) _ = function2 "and"
    (.||) _ = function2 "or"
    (.!) _ = function1 "not"
    (.=>) _ = function2 "=>"
    (.<=>) _ = function2 "="

    (.+) _ = function2 "+"
    (.-) _ = function2 "-"
    (.*) _ = function2 "*"
    (./) _ = function2 "/"
    smtQuot _ = function2 "div"
    smtModulo _ = function2 "mod"
    smtSqrt _ x = "(^ " ++ x ++ " 0.5)" 
    neg _ = function1 "-"

    itor _ = function1 "to_real"

    ite _ = function3 "ite"

    int _ x = if x >= 0 then show x else "(- " ++ show (abs x) ++ ")"
    float _ r = 
        "(/ " ++ show (numerator r) ++ " " ++ show (denominator r) ++ ")"
    double _ r =
        "(/ " ++ show (numerator r) ++ " " ++ show (denominator r) ++ ")"
    bool _ b = if b then "true" else "false"
    var _ n = function1 n

    sortInt _ = "Int"
    sortFloat _ = "Real"
    sortDouble _ = "Real"
    sortBool _ = "Bool"

    cons _ n asts _ =
        if asts /= [] then
            "(" ++ n ++ " " ++ (intercalate " " asts) ++ ")" 
        else
            n
    varName _ n _ = n

functionList :: String -> [String] -> String
functionList f xs = "(" ++ f ++ " " ++ (intercalate " " xs) ++ ")" 

function1 :: String -> String -> String
function1 f a = "(" ++ f ++ " " ++ a ++ ")"

function2 :: String -> String -> String -> String
function2 f a b = "(" ++ f ++ " " ++ a ++ " " ++ b ++ ")"

function3 :: String -> String -> String -> String -> String
function3 f a b c = "(" ++ f ++ " " ++ a ++ " " ++ b ++ " " ++ c ++ ")"

--TODO: SAME AS sortName in language, fix
sortN :: SMTConverter con ast out io => con -> Sort -> ast
sortN smtc SortInt = sortInt smtc
sortN smtc SortFloat = sortFloat smtc
sortN smtc SortDouble = sortDouble smtc
sortN smtc SortBool = sortBool smtc

selectorName :: SMTConverter con SMTName out io => con ->  Sort -> SMTName
selectorName smtc SortInt = sortInt smtc
selectorName smtc SortFloat = sortFloat smtc
selectorName smtc SortDouble = sortDouble smtc
selectorName smtc SortBool = sortBool smtc

-- | getProcessHandles
-- Ideally, this function should be called only once, and the same Handles should be used
-- in all future calls
getProcessHandles :: CreateProcess -> IO (Handle, Handle, ProcessHandle)
getProcessHandles pr = do
    (m_h_in, m_h_out, _, p) <- createProcess (pr)
        { std_in = CreatePipe, std_out = CreatePipe }

    let (h_in, h_out) =
            case (m_h_in, m_h_out) of
                (Just i, Just o) -> (i, o)
                _ -> error "Pipes to shell not successfully created."

    hSetBuffering h_in LineBuffering

    return (h_in, h_out, p)

getSMT :: Config -> IO (SomeSMT (Handle, Handle, ProcessHandle), (Handle, Handle, ProcessHandle))
getSMT (Config {smt = ConZ3}) = do
    hpp <- getZ3ProcessHandles
    return (SomeSMT Z3, hpp)
getSMT (Config {smt = ConCVC4}) = do
    hpp <- getCVC4ProcessHandles
    return (SomeSMT CVC4, hpp)

-- | getZ3ProcessHandles
-- This calls Z3, and get's it running in command line mode.  Then you can read/write on the
-- returned handles to interact with Z3
-- Ideally, this function should be called only once, and the same Handles should be used
-- in all future calls
getZ3ProcessHandles :: IO (Handle, Handle, ProcessHandle)
getZ3ProcessHandles = getProcessHandles $ proc "z3" ["-smt2", "-in"]

getCVC4ProcessHandles :: IO (Handle, Handle, ProcessHandle)
getCVC4ProcessHandles = getProcessHandles $ proc "cvc4" ["--lang", "smt2.6", "--produce-models"]

-- | setUpFormulaZ3
-- Writes a function to Z3
setUpFormulaZ3 :: Handle -> String -> IO ()
setUpFormulaZ3 h_in form = do
    hPutStr h_in "(reset)"
    hPutStr h_in form

setUpFormulaCVC4 :: Handle -> String -> IO ()
setUpFormulaCVC4 h_in form = do
    hPutStr h_in "(reset)"
    -- hPutStr h_in "(set-logic ALL)\n"
    hPutStr h_in form

-- Checks if a formula, previously written by setUp formula, is SAT
checkSat' :: Handle -> Handle -> IO Result
checkSat' h_in h_out = do
    hPutStr h_in "(check-sat)\n"

    r <- hWaitForInput h_out (-1)
    if r then do
        out <- hGetLine h_out
        -- putStrLn $ "Z3 out: " ++ out
        _ <- evaluate (length out)

        if out == "sat" then
            return SAT
        else if out == "unsat" then
            return UNSAT
        else
            return (Unknown out)
    else do
        return (Unknown "")

parseModel :: [SMTHeader] -> [(SMTName, String, Sort)] -> Model
parseModel headers = foldr (\(n, s) -> M.insert n s) M.empty
    . map (\(n, str, s) -> (n, parseToSMTAST headers str s))

parseToSMTAST :: [SMTHeader] -> String -> Sort -> SMTAST
parseToSMTAST headers str s = correctTypes s . parseGetValues $ str
    where
        correctTypes :: Sort -> SMTAST -> SMTAST
        correctTypes (SortFloat) (VDouble r) = VFloat r
        correctTypes (SortDouble) (VFloat r) = VDouble r
        correctTypes _ a = a

getModelZ3 :: Handle -> Handle -> [(SMTName, Sort)] -> IO [(SMTName, String, Sort)]
getModelZ3 h_in h_out ns = do
    hPutStr h_in "(set-option :model_evaluator.completion true)\n"
    getModel' ns
    where
        getModel' :: [(SMTName, Sort)] -> IO [(SMTName, String, Sort)]
        getModel' [] = return []
        getModel' ((n, s):nss) = do
            hPutStr h_in ("(get-value (" ++ n ++ "))\n") -- hPutStr h_in ("(eval " ++ n ++ " :completion)\n")
            out <- getLinesMatchParens h_out
            _ <- evaluate (length out) --Forces reading/avoids problems caused by laziness

            return . (:) (n, out, s) =<< getModel' nss

getModelCVC4 :: Handle -> Handle -> [(SMTName, Sort)] -> IO [(SMTName, String, Sort)]
getModelCVC4 h_in h_out ns = do
    getModel' ns
    where
        getModel' :: [(SMTName, Sort)] -> IO [(SMTName, String, Sort)]
        getModel' [] = return []
        getModel' ((n, s):nss) = do
            hPutStr h_in ("(get-value (" ++ n ++ "))\n")
            out <- getLinesMatchParens h_out
            _ <- evaluate (length out) --Forces reading/avoids problems caused by laziness

            return . (:) (n, out, s) =<< getModel' nss

getLinesMatchParens :: Handle -> IO String
getLinesMatchParens h_out = getLinesMatchParens' h_out 0

getLinesMatchParens' :: Handle -> Int -> IO String
getLinesMatchParens' h_out n = do
    out <- hGetLine h_out
    _ <- evaluate (length out)

    let open = countElem '(' out
    let close = countElem ')' out
    let n' = n + open - close

    if n' == 0 then
        return out
    else do
        out' <- getLinesMatchParens' h_out n'
        return $ out ++ out'

solveExpr :: SMTConverter con [Char] out io => Handle -> Handle -> con -> [SMTHeader] -> ExprEnv -> Expr -> IO Expr
solveExpr h_in h_out con headers eenv e = do
    let vs = symbVars eenv e
    vs' <- solveExpr' h_in h_out con headers vs
    let vs'' = map smtastToExpr vs'
    
    return $ foldr (uncurry replaceASTs) e (zip vs vs'')

solveExpr'  :: SMTConverter con [Char] out io => Handle -> Handle -> con -> [SMTHeader] -> [Expr] -> IO [SMTAST]
solveExpr' _ _ _ _ [] = return []
solveExpr' h_in h_out con headers (v:vs) = do
    v' <- solveExpr'' h_in h_out con headers v
    vs' <- solveExpr' h_in h_out con headers vs
    return (v':vs')

solveExpr'' :: SMTConverter con [Char] out io => Handle -> Handle -> con -> [SMTHeader] -> Expr -> IO SMTAST
solveExpr'' h_in h_out con headers e = do
    let smte = toSolverAST con $ exprToSMT e
    hPutStr h_in ("(eval " ++ smte ++ " :completion)\n")
    out <- getLinesMatchParens h_out
    _ <- evaluate (length out)

    return $ parseToSMTAST headers out (typeToSMT . typeOf $ e)
