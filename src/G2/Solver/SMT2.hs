-- | This defines an SMTConverter for the SMT2 language
-- It provides methods to construct formulas, as well as feed them to an external solver

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}

module G2.Solver.SMT2 where

import G2.Config.Config
import G2.Language.ArbValueGen
import G2.Language.Expr
import G2.Language.Support
import G2.Language.Syntax hiding (Assert)
import G2.Language.Typing
import G2.Solver.Language
import G2.Solver.ParseSMT
import G2.Solver.Solver
import G2.Solver.Converters --It would be nice to not import this...

import Control.Exception.Base (evaluate)
import Data.List
import Data.List.Utils (countElem)
import qualified Data.HashSet as HS
import qualified Data.Map as M
import Data.Ratio
import qualified Data.Text as T
import qualified Text.Builder as TB
import System.IO
import System.Process

data Z3 = Z3 ArbValueFunc (Handle, Handle, ProcessHandle)
data CVC4 = CVC4 ArbValueFunc (Handle, Handle, ProcessHandle)

data SomeSMTSolver where
    SomeSMTSolver :: forall con ast out io 
                   . SMTConverter con ast out io => con -> SomeSMTSolver

instance Solver Z3 where
    check solver _ pc = checkConstraintsPC solver pc
    solve con@(Z3 avf _) = checkModelPC avf con
    close = closeIO

instance Solver CVC4 where
    check solver _ pc = checkConstraintsPC solver pc
    solve con@(CVC4 avf _) = checkModelPC avf con
    close = closeIO

instance SMTConverter Z3 String String (Handle, Handle, ProcessHandle) where
    getIO (Z3 _ hhp) = hhp
    closeIO (Z3 _ (h_in, h_out, ph)) = do
        hPutStr h_in "(exit)"
        hClose h_in
        hClose h_out

    empty _ = ""  
    merge _ x y = x ++ "\n" ++ y

    checkSat _ (h_in, h_out, _) formula = do
        -- putStrLn "checkSat"
        -- putStrLn formula
        
        setUpFormulaZ3 h_in formula
        r <- checkSat' h_in h_out

        -- putStrLn $ show r

        return r

    checkSatGetModel _ (h_in, h_out, _) formula vs = do
        setUpFormulaZ3 h_in formula
        -- putStrLn "\n\n checkSatGetModel"
        -- putStrLn formula
        r <- checkSat' h_in h_out
        -- putStrLn $ "r =  " ++ show r
        case r of
            SAT () -> do
                mdl <- getModelZ3 h_in h_out vs
                -- putStrLn "======"
                -- putStrLn (show mdl)
                let m = parseModel mdl
                -- putStrLn $ "m = " ++ show m
                -- putStrLn "======"
                return $ SAT m
            UNSAT () -> return $ UNSAT ()
            Unknown s -> return $ Unknown s

    checkSatGetModelOrUnsatCore con hvals@(h_in, h_out, _) formula vs = do
        let formula' = "(set-option :produce-unsat-cores true)\n" ++ formula
        putStrLn "\n\n checkSatGetModelOrUnsatCore"
        putStrLn formula'
        setUpFormulaZ3 h_in formula'
        r <- checkSat' h_in h_out
        -- putStrLn $ "r =  " ++ show r
        if r == SAT () then do
            mdl <- getModelZ3 h_in h_out vs
            putStrLn "======"
            -- putStrLn (show mdl)
            let m = parseModel mdl
            putStrLn $ "m = " ++ show m
            putStrLn "======"
            return (SAT m)
        else if r == UNSAT () then do
            uc <- getUnsatCoreZ3 h_in h_out
            return (UNSAT $ HS.fromList uc)
        else
            return (Unknown "")

    checkSatGetModelGetExpr con (h_in, h_out, _) formula _ vs eenv (CurrExpr _ e) = do
        setUpFormulaZ3 h_in formula
        -- putStrLn "\n\n checkSatGetModelGetExpr"
        -- putStrLn formula
        r <- checkSat' h_in h_out
        -- putStrLn $ "r =  " ++ show r
        case r of
            SAT () -> do
                mdl <- getModelZ3 h_in h_out vs
                -- putStrLn "======"
                -- putStrLn formula
                -- putStrLn ""
                -- putStrLn (show mdl)
                -- putStrLn "======"
                let m = parseModel mdl

                expr <- solveExpr h_in h_out con eenv e
                -- putStrLn (show expr)
                return (SAT m, Just expr)
            UNSAT () -> return (UNSAT (), Nothing)
            Unknown s -> return (Unknown s, Nothing)

    assertSolver _ = function1 "assert"
    assertSoftSolver _ = function1 "assert-soft"

    defineFun con fn ars ret body =
        "(define-fun " ++ fn ++ " ("
            ++ intercalate " " (map (\(n, s) -> "(" ++ n ++ " " ++ sortName con s ++ ")") ars) ++ ")"
            ++ " (" ++ sortName con ret ++ ") " ++ toSolverAST con body ++ ")"

    declareFun con fn ars ret =
        "(declare-fun " ++ fn ++ " ("
            ++ intercalate " " (map (sortName con) ars) ++ ")"
            ++ " (" ++ sortName con ret ++ "))"

    varDecl _ n s = "(declare-const " ++ (T.unpack (TB.run n)) ++ " " ++ s ++ ")"
    
    setLogic _ lgc =
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
        case lgc of
            ALL -> ""
            _ -> "(set-logic " ++ s ++ ")"

    comment _ s = "; " ++ s

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

    smtFunc _ n [] = n
    smtFunc _ n xs = "(" ++ n ++ " " ++ intercalate " " xs ++  ")"

    strLen _ = function1 "str.len"

    itor _ = function1 "to_real"


    ite _ = function3 "ite"

    int _ x = if x >= 0 then show x else "(- " ++ show (abs x) ++ ")"
    float _ r = 
        "(/ " ++ show (numerator r) ++ " " ++ show (denominator r) ++ ")"
    double _ r =
        "(/ " ++ show (numerator r) ++ " " ++ show (denominator r) ++ ")"
    char _ c = '"':c:'"':[]
    bool _ b = if b then "true" else "false"
    var _ n = function1 n

    sortInt _ = "Int"
    sortFloat _ = "Real"
    sortDouble _ = "Real"
    sortChar _ = "String"
    sortBool _ = "Bool"

    cons _ n asts _ =
        if asts /= [] then
            "(" ++ n ++ " " ++ (intercalate " " asts) ++ ")" 
        else
            n
    varName _ n _ = n

    named _ ast n = "(! " ++ ast ++ " :named " ++ n ++ ")"


instance SMTConverter CVC4 String String (Handle, Handle, ProcessHandle) where
    getIO (CVC4 _ hhp) = hhp
    closeIO (CVC4 _ (h_in, h_out, ph)) = do
        hPutStr h_in "(exit)"
        hClose h_in
        hClose h_out

    empty _ = ""  
    merge _ = (++)

    checkSat _ (h_in, h_out, _) formula = do
        -- putStrLn "checkSat"
        -- putStrLn formula
        
        setUpFormulaCVC4 h_in formula
        r <- checkSat' h_in h_out

        -- putStrLn $ show r

        return r

    checkSatGetModel _ (h_in, h_out, _) formula vs = do
        setUpFormulaCVC4 h_in formula
        -- putStrLn "\n\n checkSatGetModel"
        -- putStrLn formula
        r <- checkSat' h_in h_out
        -- putStrLn $ "r =  " ++ show r
        case r of
            SAT _ -> do
                mdl <- getModelCVC4 h_in h_out vs
                -- putStrLn "======"
                -- putStrLn (show mdl)
                let m = parseModel mdl
                -- putStrLn $ "m = " ++ show m
                -- putStrLn "======"
                return (SAT m)
            UNSAT _ ->  return $ UNSAT ()
            Unknown s -> return $ Unknown s

    checkSatGetModelGetExpr con (h_in, h_out, _) formula _ vs eenv (CurrExpr _ e) = do
        setUpFormulaCVC4 h_in formula
        -- putStrLn "\n\n checkSatGetModelGetExpr"
        -- putStrLn formula
        r <- checkSat' h_in h_out
        -- putStrLn $ "r =  " ++ show r
        case r of
            SAT _ -> do
                mdl <- getModelCVC4 h_in h_out vs
                -- putStrLn "======"
                -- putStrLn formula
                -- putStrLn ""
                -- putStrLn (show mdl)
                -- putStrLn "======"
                let m = parseModel mdl

                expr <- solveExpr h_in h_out con eenv e
                -- putStrLn (show expr)
                return (SAT m, Just expr)
            UNSAT _ -> return (UNSAT (), Nothing)
            Unknown s -> return (Unknown s, Nothing)

    assertSolver _ = function1 "assert"
        
    varDecl _ n s = "(declare-const " ++ (T.unpack (TB.run n)) ++ " " ++ s ++ ")"
    
    setLogic _ lgc =
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
    strLen _ = function1 "str.len"

    itor _ = function1 "to_real"

    ite _ = function3 "ite"

    int _ x = if x >= 0 then show x else "(- " ++ show (abs x) ++ ")"
    float _ r = 
        "(/ " ++ show (numerator r) ++ " " ++ show (denominator r) ++ ")"
    double _ r =
        "(/ " ++ show (numerator r) ++ " " ++ show (denominator r) ++ ")"
    char _ c = '"':c:'"':[]
    bool _ b = if b then "true" else "false"
    var _ n = function1 n

    sortInt _ = "Int"
    sortFloat _ = "Real"
    sortDouble _ = "Real"
    sortChar _ = "String"
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

-- | getProcessHandles
-- Ideally, this function should be called only once, and the same Handles should be used
-- in all future calls
getProcessHandles :: CreateProcess -> IO (Handle, Handle, ProcessHandle)
getProcessHandles pr = do
    (m_h_in, m_h_out, h_err, p) <- createProcess (pr)
        { std_in = CreatePipe, std_out = CreatePipe }

    case h_err of
        Just h_err' -> hClose h_err'
        Nothing -> return ()

    let (h_in, h_out) =
            case (m_h_in, m_h_out) of
                (Just i, Just o) -> (i, o)
                _ -> error "Pipes to shell not successfully created."

    hSetBuffering h_in LineBuffering

    return (h_in, h_out, p)

getSMT :: Config -> IO SomeSMTSolver
getSMT = getSMTAV arbValue

getSMTInfinite :: Config -> IO SomeSMTSolver
getSMTInfinite = getSMTAV arbValueInfinite

getSMTAV :: ArbValueFunc -> Config -> IO SomeSMTSolver
getSMTAV avf (Config {smt = ConZ3}) = do
    hhp@(h_in, _, _) <- getZ3ProcessHandles
    hPutStr h_in "(set-option :pp.decimal true)"
    return $ SomeSMTSolver (Z3 avf hhp)
getSMTAV avf (Config {smt = ConCVC4}) = do
    hhp <- getCVC4ProcessHandles
    return $ SomeSMTSolver (CVC4 avf hhp)

-- | getZ3ProcessHandles
-- This calls Z3, and get's it running in command line mode.  Then you can read/write on the
-- returned handles to interact with Z3
-- Ideally, this function should be called only once, and the same Handles should be used
-- in all future calls
getZ3ProcessHandles :: IO (Handle, Handle, ProcessHandle)
getZ3ProcessHandles = getProcessHandles $ proc "z3" ["-smt2", "-in", "-t:10000"]

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
checkSat' :: Handle -> Handle -> IO (Result () ())
checkSat' h_in h_out = do
    hPutStr h_in "(check-sat)\n"

    r <- hWaitForInput h_out (-1)
    if r then do
        out <- hGetLine h_out
        -- putStrLn $ "Z3 out: " ++ out
        _ <- evaluate (length out)

        if out == "sat" then
            return $ SAT ()
        else if out == "unsat" then
            return $ UNSAT ()
        else
            return (Unknown out)
    else do
        return (Unknown "")

parseModel :: [(SMTName, String, Sort)] -> SMTModel
parseModel = foldr (\(n, s) -> M.insert n s) M.empty
    . map (\(n, str, s) -> (n, parseToSMTAST str s))

parseToSMTAST :: String -> Sort -> SMTAST
parseToSMTAST str s = correctTypes s . parseGetValues $ str
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

getUnsatCoreZ3 :: Handle -> Handle -> IO [SMTName]
getUnsatCoreZ3 h_in h_out = do
    hPutStr h_in "(get-unsat-core)\n"
    r <- hWaitForInput h_out (-1)
    out <- hGetLine h_out 
    putStrLn $ "unsat-core = " ++ out
    let out' = tail . init $ out -- drop opening and closing parens
    return $ words out' 

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
    let clse = countElem ')' out
    let n' = n + open - clse

    if n' == 0 then
        return out
    else do
        out' <- getLinesMatchParens' h_out n'
        return $ out ++ out'

solveExpr :: SMTConverter con [Char] out io => Handle -> Handle -> con -> ExprEnv -> Expr -> IO Expr
solveExpr h_in h_out con eenv e = do
    let vs = symbVars eenv e
    vs' <- solveExpr' h_in h_out con vs
    let vs'' = map smtastToExpr vs'
    
    return $ foldr (uncurry replaceASTs) e (zip vs vs'')

solveExpr'  :: SMTConverter con [Char] out io => Handle -> Handle -> con -> [Expr] -> IO [SMTAST]
solveExpr' _ _ _ [] = return []
solveExpr' h_in h_out con (v:vs) = do
    v' <- solveExpr'' h_in h_out con v
    vs' <- solveExpr' h_in h_out con vs
    return (v':vs')

solveExpr'' :: SMTConverter con [Char] out io => Handle -> Handle -> con -> Expr -> IO SMTAST
solveExpr'' h_in h_out con e = do
    let smte = toSolverAST con $ exprToSMT e
    hPutStr h_in ("(eval " ++ smte ++ " :completion)\n")
    out <- getLinesMatchParens h_out
    _ <- evaluate (length out)

    return $ parseToSMTAST out (typeToSMT . typeOf $ e)