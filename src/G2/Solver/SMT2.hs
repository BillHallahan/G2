-- | This defines an SMTConverter for the SMT2 language
-- It provides methods to construct formulas, as well as feed them to an external solver

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}

module G2.Solver.SMT2 ( Z3
                      , CVC4
                      , SomeSMTSolver (..)
                      , getZ3
                      , getSMT
                      , getSMTAV) where

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
import Data.List.Utils (countElem)
import qualified Data.HashSet as HS
import Data.IORef
import qualified Data.Map as M
import Data.Ratio
import Data.Semigroup
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Text.Builder as TB
import System.IO
import System.Process

data Z3 = Z3 ArbValueFunc (Handle, Handle, ProcessHandle)
data CVC4 = CVC4 ArbValueFunc (Handle, Handle, ProcessHandle)

data SomeSMTSolver where
    SomeSMTSolver :: forall con
                   . SMTConverter con => con -> SomeSMTSolver

instance Solver Z3 where
    check solver _ pc = checkConstraintsPC solver pc
    solve con@(Z3 avf _) = checkModelPC avf con
    close = closeIO

instance Solver CVC4 where
    check solver _ pc = checkConstraintsPC solver pc
    solve con@(CVC4 avf _) = checkModelPC avf con
    close = closeIO

getIOZ3 :: Z3 -> (Handle, Handle, ProcessHandle)
getIOZ3 (Z3 _ hhp) = hhp

instance SMTConverter Z3 where
    closeIO (Z3 _ (h_in, h_out, ph)) = do
        T.hPutStrLn h_in "(exit)"
        _ <- waitForProcess ph
        hClose h_in
        hClose h_out

    reset con = do
        let (h_in, _, _) = getIOZ3 con
        T.hPutStr h_in "(reset)"

    checkSatInstr con = do
        let (h_in, _, _) = getIOZ3 con
        T.hPutStrLn h_in "(check-sat)"

    maybeCheckSatResult con = do
        let (_, h_out, _) = getIOZ3 con
        r <- hReady h_out
        case r of
            True -> return . Just =<< checkSatReadResult h_out
            False -> return Nothing

    getModelInstrResult con vs = do
        let (h_in, h_out, _) = getIOZ3 con
        mdl <- getModelZ3 h_in h_out vs
        -- putStrLn "======"
        -- putStrLn (show mdl)
        let m = parseModel mdl
        -- putStrLn $ "m = " ++ show m
        -- putStrLn "======"
        return m

    getUnsatCoreInstrResult con = do
        let (h_in, h_out, _) = getIOZ3 con
        uc <- getUnsatCoreZ3 h_in h_out
        return (HS.fromList uc)

    setProduceUnsatCores con = do
        let (h_in, _, _) = getIOZ3 con
        T.hPutStrLn h_in "(set-option :produce-unsat-cores true)"

    addFormula con form = do
        let (h_in, _, _) = getIOZ3 con
        T.hPutStrLn h_in (TB.run $ toSolverText form)

    checkSat con formula = do
        let (h_in, h_out, _) = getIOZ3 con
        -- putStrLn "checkSat"
        -- let formula = run formulaBldr
        -- T.putStrLn (TB.run formula)
        -- putStrLn formula
        
        setUpFormulaZ3 h_in (TB.run $ toSolverText formula)
        r <- checkSat' h_in h_out

        -- putStrLn $ show r

        return r

    checkSatGetModel con formula vs = do
        let (h_in, h_out, _) = getIOZ3 con
        setUpFormulaZ3 h_in (TB.run $ toSolverText formula)
        -- putStrLn "\n\n checkSatGetModel"
        -- T.putStrLn (TB.run formula)
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
            Unknown s _ -> return $ Unknown s ()

    checkSatGetModelOrUnsatCoreNoReset con formula vs = do
        let (h_in, h_out, _) = getIOZ3 con
        let formula' = TB.run $ toSolverText formula
        T.putStrLn "\n\n checkSatGetModelOrUnsatCore"
        T.putStrLn formula'

        T.hPutStr h_in formula'
        r <- checkSat' h_in h_out
        -- putStrLn $ "r =  " ++ show r
        if r == SAT () then do
            mdl <- getModelZ3 h_in h_out vs
            -- putStrLn "======"
            -- putStrLn $ "r = " ++ show r
            -- putStrLn $ "mdl = " ++ show mdl
            -- putStrLn (show mdl)
            let m = parseModel mdl
            -- putStrLn $ "m = " ++ show m
            -- putStrLn "======"
            return (SAT m)
        else if r == UNSAT () then do
            uc <- getUnsatCoreZ3 h_in h_out
            return (UNSAT $ HS.fromList uc)
        else do
            return (Unknown "" ())

    push con = do
        let (h_in, _, _) = getIOZ3 con
        T.hPutStrLn h_in "(push)"

    pop con = do
        let (h_in, _, _) = getIOZ3 con
        T.hPutStrLn h_in "(push)"

getIOCVC4 :: CVC4 -> (Handle, Handle, ProcessHandle)
getIOCVC4 (CVC4 _ hhp) = hhp

instance SMTConverter CVC4 where
    closeIO (CVC4 _ (h_in, h_out, ph)) = do
        hPutStrLn h_in "(exit)"
        _ <- waitForProcess ph
        hClose h_in
        hClose h_out

    reset con = do
        let (h_in, _, _) = getIOCVC4 con
        T.hPutStr h_in "(reset)"

    checkSatInstr con = do
        let (h_in, _, _) = getIOCVC4 con
        T.hPutStrLn h_in "(check-sat)"

    maybeCheckSatResult con = do
        let (_, h_out, _) = getIOCVC4 con
        r <- hReady h_out
        case r of
            True -> return . Just =<< checkSatReadResult h_out
            False -> return Nothing

    getModelInstrResult con vs = do
        let (h_in, h_out, _) = getIOCVC4 con
        mdl <- getModelCVC4 h_in h_out vs
        -- putStrLn "======"
        -- putStrLn (show mdl)
        let m = parseModel mdl
        -- putStrLn $ "m = " ++ show m
        -- putStrLn "======"
        return m

    getUnsatCoreInstrResult con = do
        let (h_in, h_out, _) = getIOCVC4 con
        uc <- getUnsatCoreCVC4 h_in h_out
        return (HS.fromList uc)

    setProduceUnsatCores _ = return ()

    addFormula con form = do
        let (h_in, _, _) = getIOCVC4 con
        T.hPutStrLn h_in (TB.run $ toSolverText form)

    checkSat con formula = do
        let (h_in, h_out, _) = getIOCVC4 con
        -- putStrLn "checkSat"
        -- putStrLn formula
        
        setUpFormulaCVC4 h_in (TB.run $ toSolverText formula)
        r <- checkSat' h_in h_out

        -- putStrLn $ show r

        return r

    checkSatGetModel con formula vs = do
        let (h_in, h_out, _) = getIOCVC4 con
        setUpFormulaCVC4 h_in (TB.run $ toSolverText formula)
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
            Unknown s _ -> return $ Unknown s ()

    checkSatGetModelOrUnsatCoreNoReset con formula vs = do
        let (h_in, h_out, _) = getIOCVC4 con
        let formula' = TB.run $ toSolverText formula
        T.putStrLn "\n\n checkSatGetModelOrUnsatCore"
        T.putStrLn formula'

        T.hPutStr h_in formula'
        r <- checkSat' h_in h_out
        putStrLn $ "r =  " ++ show r
        if r == SAT () then do
            mdl <- getModelCVC4 h_in h_out vs
            -- putStrLn "======"
            -- putStrLn $ "r = " ++ show r
            -- putStrLn $ "mdl = " ++ show mdl
            -- putStrLn (show mdl)
            let m = parseModel mdl
            -- putStrLn $ "m = " ++ show m
            -- putStrLn "======"
            return (SAT m)
        else if r == UNSAT () then do
            uc <- getUnsatCoreCVC4 h_in h_out
            return (UNSAT $ HS.fromList uc)
        else do
            return (Unknown "" ())

    push con = do
        let (h_in, _, _) = getIOCVC4 con
        T.hPutStrLn h_in "(push)"

    pop con = do
        let (h_in, _, _) = getIOCVC4 con
        T.hPutStrLn h_in "(push)"

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

getZ3 :: IO Z3
getZ3 = do
    hhp@(h_in, _, _) <- getZ3ProcessHandles
    hPutStr h_in "(set-option :pp.decimal true)"
    return $ Z3 arbValue hhp

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
getCVC4ProcessHandles = getProcessHandles $ proc "cvc4" ["--lang", "smt2.6", "--produce-models", "--produce-unsat-cores"]

-- | setUpFormulaZ3
-- Writes a function to Z3
setUpFormulaZ3 :: Handle -> T.Text -> IO ()
setUpFormulaZ3 h_in form = do
    T.hPutStr h_in "(reset)"
    T.hPutStr h_in form

setUpFormulaCVC4 :: Handle -> T.Text -> IO ()
setUpFormulaCVC4 h_in form = do
    T.hPutStr h_in "(reset)"
    -- hPutStr h_in "(set-logic ALL)\n"
    T.hPutStr h_in form

-- Checks if a formula, previously written by setUp formula, is SAT
checkSat' :: Handle -> Handle -> IO (Result () () ())
checkSat' h_in h_out = do
    hPutStr h_in "(check-sat)\n"

    r <- hWaitForInput h_out (-1)
    checkSatReadResult h_out

checkSatReadResult :: Handle -> IO (Result () () ())
checkSatReadResult h_out = do
    out <- hGetLine h_out
    -- putStrLn $ "Z3 out: " ++ out
    _ <- evaluate (length out)

    if out == "sat" then
        return $ SAT ()
    else if out == "unsat" then
        return $ UNSAT ()
    else
        return (Unknown out ())

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
    _ <- hWaitForInput h_out (-1)
    out <- hGetLine h_out 
    putStrLn $ "unsat-core = " ++ out
    let out' = tail . init $ out -- drop opening and closing parens

    case words out' of
        "error":_ -> error "getUnsatCoreZ3: Error producing unsat core"
        w -> return w

getUnsatCoreCVC4 :: Handle -> Handle -> IO [SMTName]
getUnsatCoreCVC4 h_in h_out = do
    hPutStr h_in "(get-unsat-core)\n"
    _ <- hWaitForInput h_out (-1)
    opening_bracket <- hGetLine h_out
    out <- getCore
    putStrLn $ "unsat-core = " ++ show out

    return out
    where
        getCore = do
            _ <- hWaitForInput h_out (-1)
            core <- hGetLine h_out
            putStrLn $ "getCore " ++ show core
            case core of
                ")" -> return []
                _ -> return . (:) core =<< getCore

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

solveExpr :: SMTConverter con => Handle -> Handle -> con -> ExprEnv -> Expr -> IO Expr
solveExpr h_in h_out con eenv e = do
    let vs = map (\i -> Var i) $ symbVars eenv e
    vs' <- solveExpr' h_in h_out con vs
    let vs'' = map smtastToExpr vs'
    
    return $ foldr (uncurry replaceASTs) e (zip vs vs'')

solveExpr'  :: SMTConverter con => Handle -> Handle -> con -> [Expr] -> IO [SMTAST]
solveExpr' _ _ _ [] = return []
solveExpr' h_in h_out con (v:vs) = do
    v' <- solveExpr'' h_in h_out con v
    vs' <- solveExpr' h_in h_out con vs
    return (v':vs')

solveExpr'' :: SMTConverter con => Handle -> Handle -> con -> Expr -> IO SMTAST
solveExpr'' h_in h_out con e = do
    let smte = toSolverAST $ exprToSMT e
    T.hPutStr h_in ("(eval " <> TB.run smte <> " :completion)\n")
    out <- getLinesMatchParens h_out
    _ <- evaluate (length out)

    return $ parseToSMTAST out (typeToSMT . typeOf $ e)