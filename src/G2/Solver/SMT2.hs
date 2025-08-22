-- | This defines an SMTConverter for the SMT2 language
-- It provides methods to construct formulas, as well as feed them to an external solver

{-# LANGUAGE BangPatterns, CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module G2.Solver.SMT2 ( Z3StringSolver (..)
                      , Z3
                      , CVC5
                      , SomeSMTSolver (..)
                      , getZ3
                      , getSMT
                      , getSMTAV) where

import G2.Config.Config
import G2.Language.ArbValueGen
import G2.Solver.Language
import G2.Solver.ParseSMT
import G2.Solver.Solver
import G2.Solver.Converters --It would be nice to not import this...

import Control.Exception.Base (evaluate)
import Control.Monad
import Data.List.Utils (countElem)
import qualified Data.HashSet as HS
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Text.Builder as TB
import System.IO
import System.Process
import Data.Maybe (fromMaybe)

data Z3StringSolver = SeqSolver | Z3Str3 deriving Eq
data Z3 = Z3 Z3StringSolver PrintSMT ArbValueFunc (Handle, Handle, ProcessHandle)


data CVC5 = CVC5 PrintSMT ArbValueFunc (Handle, Handle, ProcessHandle)
data Ostrich = Ostrich PrintSMT ArbValueFunc (Handle, Handle, ProcessHandle)

data SomeSMTSolver where
    SomeSMTSolver :: forall con
                   . SMTConverter con => con -> SomeSMTSolver

instance Solver Z3 where
    check solver _ pc = checkConstraintsPC solver pc
    solve con@(Z3 _ _ avf _) = checkModelPC avf con
    close = closeIO

instance Solver CVC5 where
    check solver _ pc = checkConstraintsPC solver pc
    solve con@(CVC5 _ avf _) = checkModelPC avf con
    close = closeIO

instance Solver Ostrich where
    check solver _ pc = checkConstraintsPC solver pc
    solve con@(Ostrich _ avf _) = checkModelPC avf con
    close = closeIO

instance SMTConverter Z3 where
    getIO (Z3 _ _ _ hhp) = hhp
    getPrintSMT (Z3 _ print_smt _ _) = print_smt

    closeIO (Z3 _ _ _ (h_in, h_out, ph)) = do
#if MIN_VERSION_process(1,6,4)
        cleanupProcess (Just h_in, Just h_out, Nothing, ph)
#else
        T.hPutStrLn h_in "(exit)"
        _ <- waitForProcess ph
        hClose h_in
        hClose h_out
#endif

    reset con@(Z3 string_solver print_smt _ _) = do
        let (h_in, _, _) = getIO con
        when print_smt $ putStrLn "(reset)"
        T.hPutStr h_in "(reset)"
        
        when (string_solver == Z3Str3) $ do
            when print_smt $ putStrLn "(set-option :smt.string_solver z3str3)"
            T.hPutStr h_in "(set-option :smt.string_solver z3str3)"

    checkSatInstr con = do
        let (h_in, _, _) = getIO con
        T.hPutStrLn h_in "(check-sat)"

    maybeCheckSatResult con = do
        let (_, h_out, _) = getIO con
        r <- hReady h_out
        case r of
            True -> return . Just =<< checkSatReadResult h_out
            False -> return Nothing

    getModelInstrResult con@(Z3 _ print_smt _ _) vs = do
        let (h_in, h_out, _) = getIO con
        mdl <- getModelZ3 print_smt h_in h_out vs
        -- putStrLn "======"
        -- putStrLn (show mdl)
        let m = parseModel mdl
        -- putStrLn $ "m = " ++ show m
        -- putStrLn "======"
        return m

    getUnsatCoreInstrResult con = do
        let (h_in, h_out, _) = getIO con
        uc <- getUnsatCoreZ3 h_in h_out
        return (HS.fromList uc)

    setProduceUnsatCores con = do
        let (h_in, _, _) = getIO con
        T.hPutStrLn h_in "(set-option :produce-unsat-cores true)"

    addFormula = stdAddFormula

    checkSatNoReset = stdCheckSatNoReset

    checkSatGetModel con@(Z3 _ print_smt _ _) formula vs = do
        let (h_in, h_out, _) = getIO con
        reset con        
        when print_smt $ T.putStrLn (TB.run $ toSolverText formula)
        T.hPutStr h_in (TB.run $ toSolverText formula)

        r <- checkSat' print_smt h_in h_out
        when print_smt (putStrLn $ show r)

        case r of
            SAT () -> do
                mdl <- getModelZ3 print_smt h_in h_out vs
                when print_smt (putStrLn $ "model =  " ++ show (map (\(_, v, _) -> v) mdl))
                let m = parseModel mdl
                return $ SAT m
            UNSAT () -> return $ UNSAT ()
            Unknown s _ -> return $ Unknown s ()

    checkSatGetModelOrUnsatCoreNoReset con@(Z3 _ print_smt _ _) formula vs = do
        let (h_in, h_out, _) = getIO con
        let formula' = TB.run $ toSolverText formula
        T.putStrLn "\n\n checkSatGetModelOrUnsatCore"
        T.putStrLn formula'

        T.hPutStr h_in formula'
        r <- checkSat' print_smt h_in h_out
        if r == SAT () then do
            mdl <- getModelZ3 print_smt h_in h_out vs
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

    push = stdPush
    pop = stdPop

instance SMTConverter CVC5 where
    getIO (CVC5 _ _ hhp) = hhp
    getPrintSMT (CVC5 print_smt _ _) = print_smt

    closeIO (CVC5 _ _ (h_in, h_out, ph)) = do
        hPutStrLn h_in "(exit)"
        _ <- waitForProcess ph
        hClose h_in
        hClose h_out

    reset con@(CVC5 print_smt _ _) = do
        let (h_in, _, _) = getIO con
        when print_smt $ putStrLn "(reset)"
        T.hPutStr h_in "(reset)"

    checkSatInstr con = do
        let (h_in, _, _) = getIO con
        T.hPutStrLn h_in "(check-sat)"

    maybeCheckSatResult con = do
        let (_, h_out, _) = getIO con
        r <- hReady h_out
        case r of
            True -> return . Just =<< checkSatReadResult h_out
            False -> return Nothing

    getModelInstrResult con@(CVC5 print_smt _ _) vs = do
        let (h_in, h_out, _) = getIO con
        mdl <- getModel print_smt h_in h_out vs
        -- putStrLn "======"
        -- putStrLn (show mdl)
        let m = parseModel mdl
        -- putStrLn $ "m = " ++ show m
        -- putStrLn "======"
        return m

    getUnsatCoreInstrResult con = do
        let (h_in, h_out, _) = getIO con
        uc <- getUnsatCoreCVC5 h_in h_out
        return (HS.fromList uc)

    setProduceUnsatCores _ = return ()

    addFormula = stdAddFormula

    checkSatNoReset = stdCheckSatNoReset

    checkSatGetModel con@(CVC5 print_smt _ _) formula vs = do
        let (h_in, h_out, _) = getIO con
        reset con
        when print_smt $ T.putStrLn (TB.run $ toSolverText formula)
        T.hPutStr h_in (TB.run $ toSolverText formula)
        r <- checkSat' print_smt h_in h_out
        when print_smt (putStrLn $ show r)
        case r of
            SAT _ -> do
                mdl <- getModel print_smt h_in h_out vs
                -- putStrLn "======"
                -- putStrLn (show mdl)
                let m = parseModel mdl
                -- putStrLn $ "m = " ++ show m
                -- putStrLn "======"
                return (SAT m)
            UNSAT _ ->  return $ UNSAT ()
            Unknown s _ -> return $ Unknown s ()

    checkSatGetModelOrUnsatCoreNoReset con@(CVC5 print_smt _ _) formula vs = do
        let (h_in, h_out, _) = getIO con
        let formula' = TB.run $ toSolverText formula
        T.putStrLn "\n\n checkSatGetModelOrUnsatCore"
        T.putStrLn formula'

        T.hPutStr h_in formula'
        r <- checkSat' print_smt h_in h_out
        if r == SAT () then do
            mdl <- getModel print_smt h_in h_out vs
            -- putStrLn "======"
            -- putStrLn $ "r = " ++ show r
            -- putStrLn $ "mdl = " ++ show mdl
            -- putStrLn (show mdl)
            let m = parseModel mdl
            -- putStrLn $ "m = " ++ show m
            -- putStrLn "======"
            return (SAT m)
        else if r == UNSAT () then do
            uc <- getUnsatCoreCVC5 h_in h_out
            return (UNSAT $ HS.fromList uc)
        else do
            return (Unknown "" ())

    push = stdPush
    pop = stdPop

instance SMTConverter Ostrich where
    getIO (Ostrich _ _ hhp) = hhp
    getPrintSMT (Ostrich print_smt _ _) = print_smt

    closeIO (Ostrich _ _ (h_in, h_out, ph)) = do
#if MIN_VERSION_process(1,6,4)
        cleanupProcess (Just h_in, Just h_out, Nothing, ph)
#else
        T.hPutStrLn h_in "(exit)"
        _ <- waitForProcess ph
        hClose h_in
        hClose h_out
#endif
    reset con@(Ostrich print_smt _ _) = do
        let (h_in, _, _) = getIO con
        when print_smt $ putStrLn "(reset)"
        T.hPutStr h_in "(reset)"

    checkSatInstr con = do
        let (h_in, _, _) = getIO con
        T.hPutStrLn h_in "(check-sat)"

    maybeCheckSatResult con = do
        let (_, h_out, _) = getIO con
        r <- hReady h_out
        case r of
            True -> return . Just =<< checkSatReadResult h_out
            False -> return Nothing

    getModelInstrResult con@(Ostrich print_smt _ _) vs = do
        let (h_in, h_out, _) = getIO con
        mdl <- getModel print_smt h_in h_out vs
        -- putStrLn "======"
        -- putStrLn (show mdl)
        let m = parseModel mdl
        -- putStrLn $ "m = " ++ show m
        -- putStrLn "======"
        return m

    getUnsatCoreInstrResult _ = error "ostrich: unsat core not supported"
    setProduceUnsatCores _ = error "ostrich: unsat core not supported"

    addFormula = stdAddFormula

    checkSatNoReset = stdCheckSatNoReset

    checkSatGetModel con@(Ostrich print_smt _ _) formula vs = do
        let (h_in, h_out, _) = getIO con
        reset con
        T.hPutStr h_in (TB.run $ toSolverText formula)
        
        when print_smt $ do
            T.putStrLn (TB.run $ toSolverText formula)
        
        r <- checkSat' print_smt h_in h_out
        when print_smt (putStrLn $ show r)

        case r of
            SAT () -> do
                mdl <- getModel print_smt h_in h_out vs
                when print_smt (putStrLn $ "model =  " ++ show (map (\(_, v, _) -> v) mdl))
                let m = parseModel mdl
                return $ SAT m
            UNSAT () -> return $ UNSAT ()
            Unknown s _ -> return $ Unknown s ()

    checkSatGetModelOrUnsatCoreNoReset _ _ _ = error "ostrich: unsat core not supported"

    push = stdPush
    pop = stdPop

stdAddFormula :: SMTConverter con => con -> [SMTHeader] -> IO ()
stdAddFormula con form = do
    let (h_in, _, _) = getIO con
        pr_smt = getPrintSMT con
    when pr_smt $ T.putStrLn (TB.run $ toSolverText form)
    T.hPutStrLn h_in (TB.run $ toSolverText form)


stdCheckSatNoReset :: SMTConverter con => con -> [SMTHeader] -> IO (Result () () ())
stdCheckSatNoReset con formula = do
        let (h_in, h_out, _) = getIO con
            pr_smt = getPrintSMT con

        when pr_smt $ T.putStrLn (TB.run $ toSolverText formula)

        T.hPutStrLn h_in (TB.run $ toSolverText formula)
        r <- checkSat' pr_smt h_in h_out

        when pr_smt (putStrLn $ show r)

        return r

stdPush :: SMTConverter con => con -> IO ()
stdPush con = do
    let (h_in, _, _) = getIO con
    T.hPutStrLn h_in "(push)"

stdPop :: SMTConverter con => con -> IO ()
stdPop con = do
    let (h_in, _, _) = getIO con
    T.hPutStrLn h_in "(pop)"


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

getZ3 :: PrintSMT -> Int -> IO Z3
getZ3 pr_smt time_out = do
    hhp <- getZ3ProcessHandles Nothing time_out
    return $ Z3 SeqSolver pr_smt arbValue hhp

getSMT :: SMTConfig -> IO SomeSMTSolver
getSMT = getSMTAV arbValue

getSMTAV :: ArbValueFunc -> SMTConfig -> IO SomeSMTSolver
getSMTAV avf (SMTConfig { smt = ConZ3, smt_path = path, print_smt = pr }) = do
    hhp <- getZ3ProcessHandles path 10000
    return $ SomeSMTSolver (Z3 SeqSolver pr avf hhp)
getSMTAV avf (SMTConfig { smt = ConZ3Str3, smt_path = path, print_smt = pr }) = do
    hhp <- getZ3ProcessHandles path 10000
    return $ SomeSMTSolver (Z3 Z3Str3 pr avf hhp)
getSMTAV avf (SMTConfig { smt = ConCVC5, smt_path = path, print_smt = pr }) = do
    hhp <- getCVC5ProcessHandles path 10000
    return $ SomeSMTSolver (CVC5 pr avf hhp)
getSMTAV avf (SMTConfig { smt = ConOstrich, smt_path = path, print_smt = pr }) = do
    hhp <- getOstrichProcessHandles path 10000
    return $ SomeSMTSolver (Ostrich pr avf hhp)

-- | getZ3ProcessHandles
-- This calls Z3, and get's it running in command line mode.  Then you can read/write on the
-- returned handles to interact with Z3
-- Ideally, this function should be called only once, and the same Handles should be used
-- in all future calls
getZ3ProcessHandles :: Maybe FilePath -> Int -> IO (Handle, Handle, ProcessHandle)
getZ3ProcessHandles m_path time_out = getProcessHandles $ proc (selPath m_path "z3") ["-smt2", "-in", "-t:" ++ show time_out, "model=true"]

getCVC5ProcessHandles :: Maybe FilePath -> Int -> IO (Handle, Handle, ProcessHandle)
getCVC5ProcessHandles m_path time_out = getProcessHandles $ proc (selPath m_path "cvc5") ["--lang", "smt2.6", "--produce-models", "--produce-unsat-cores", "--tlimit-per=" ++ show time_out]

getOstrichProcessHandles :: Maybe FilePath -> Int -> IO (Handle, Handle, ProcessHandle)
getOstrichProcessHandles m_path time_out = getProcessHandles $ proc (selPath m_path "ostrich") ["+quiet", "+stdin", "+incremental", "-timeoutPer=" ++ show time_out]

selPath :: Maybe FilePath -> FilePath -> FilePath
selPath = flip fromMaybe

-- Checks if a formula, previously written by setUp formula, is SAT
checkSat' :: PrintSMT -> Handle -> Handle -> IO (Result () () ())
checkSat' print_smt h_in h_out = do
    when print_smt (putStrLn "(check-sat)")
    hPutStrLn h_in "(check-sat)"

    _ <- hWaitForInput h_out (-1)
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
parseToSMTAST str s = correctTypes s . parseGetValues s $ str
    where
        correctTypes :: Sort -> SMTAST -> SMTAST
        correctTypes SortChar (VString [c]) = VChar c
        correctTypes SortChar (VString _) = error "Invalid Char from parseToSMTAST"
        correctTypes _ a = a

getModelZ3 :: PrintSMT -> Handle -> Handle -> [(SMTName, Sort)] -> IO [(SMTName, String, Sort)]
getModelZ3 print_smt h_in h_out ns = do
    hPutStr h_in "(set-option :model_evaluator.completion true)\n"
    getModel print_smt h_in h_out ns

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

getUnsatCoreCVC5 :: Handle -> Handle -> IO [SMTName]
getUnsatCoreCVC5 h_in h_out = do
    hPutStr h_in "(get-unsat-core)\n"
    _ <- hWaitForInput h_out (-1)
    -- Read in the opening bracket
    _ <- hGetLine h_out
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

getModel :: PrintSMT -> Handle -> Handle -> [(SMTName, Sort)] -> IO [(SMTName, String, Sort)]
getModel print_smt h_in h_out ns = do
    getModel' ns
    where
        getModel' :: [(SMTName, Sort)] -> IO [(SMTName, String, Sort)]
        getModel' [] = return []
        getModel' ((n, s):nss) = do
            when print_smt (putStrLn $ "(get-value (" ++ n ++ "))")
            hPutStrLn h_in ("(get-value (" ++ n ++ "))")
            out <- getLinesMatchParens h_out
            _ <- evaluate (length out) --Forces reading/avoids problems caused by laziness

            return . (:) (n, out, s) =<< getModel' nss

getLinesMatchParens :: Handle -> IO String
getLinesMatchParens h_out = getLinesMatchParens' h_out False 0

getLinesMatchParens' :: Handle
                     -> Bool -- ^ Are we in a string?
                     -> Int -- ^ Unclosed paren count
                     -> IO String
getLinesMatchParens' h_out in_string count = do
    out <- hGetLine h_out
    _ <- evaluate (length out)

    let (count', in_string') = readCountingParen in_string count out

    if count' == 0 then
        return out
    else do
        out' <- getLinesMatchParens' h_out in_string' count'
        return $ out ++ out'


-- | Count the number of unclosed parentheses. Does not count parentheses in strings
readCountingParen :: Bool -- ^ Are we in a string?
                  -> Int -- ^ Unclosed paren count
                  -> String
                  -> (Int, Bool)
readCountingParen in_string count "" = (count, in_string)
readCountingParen False count ('(':xs) = let !count' = count + 1 in readCountingParen False count' xs
readCountingParen False count (')':xs) = let !count' = count - 1 in readCountingParen False count' xs
readCountingParen in_string count ('"':'"':xs) = readCountingParen in_string count xs
readCountingParen in_string count ('"':xs) = readCountingParen (not in_string) count xs
readCountingParen in_string count (_:xs) = readCountingParen in_string count xs