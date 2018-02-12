-- | This defines an SMTConverter for the SMT2 language
-- It provides methods to construct formulas, as well as feed them to an external solver
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

import Debug.Trace

type SMT2Converter = SMTConverter String String (Handle, Handle, ProcessHandle)

z3 :: SMT2Converter
z3 = smt2 setUpFormulaZ3 getModelZ3

cvc4 :: SMT2Converter
cvc4 = smt2 setUpFormulaCVC4 getModelCVC4

smt2 :: (Handle -> String -> IO ())
     -> (Handle -> Handle -> [(SMTName, Sort)] -> IO [(SMTName, String, Sort)])
     -> SMT2Converter
smt2 setup getmdl = SMTConverter {
          empty = ""  
        , merge = (++)

        , checkSat = \(h_in, h_out, _) formula -> do
            -- putStrLn "checkSat"
            -- putStrLn formula
            
            setup h_in formula
            r <- checkSat' h_in h_out

            -- putStrLn $ show r

            return r

        , checkSatGetModel = \(h_in, h_out, _) formula headers vs -> do
            setup h_in formula
            -- putStrLn "\n\n checkSatGetModel"
            r <- checkSat' h_in h_out
            -- putStrLn $ "r =  " ++ show r
            if r == SAT then do
                mdl <- getmdl h_in h_out vs
                -- putStrLn "======"
                -- putStrLn formula
                -- putStrLn ""
                -- putStrLn (show mdl)
                let m = parseModel headers mdl
                -- putStrLn $ "m = " ++ show m
                -- putStrLn "======"
                return (r, Just m)
            else do
                return (r, Nothing)

        , checkSatGetModelGetExpr = \(h_in, h_out, _) formula headers vs eenv (CurrExpr _ e) -> do
            setup h_in formula
            -- putStrLn "\n\n checkSatGetModelGetExpr"
            -- putStrLn formula
            r <- checkSat' h_in h_out
            -- putStrLn $ "r =  " ++ show r
            if r == SAT then do
                mdl <- getmdl h_in h_out vs
                -- putStrLn "======"
                -- putStrLn formula
                -- putStrLn ""
                -- putStrLn (show mdl)
                -- putStrLn "======"
                let m = parseModel headers mdl

                expr <- solveExpr h_in h_out (smt2 setup getmdl) headers eenv e
                -- putStrLn (show expr)
                return (r, Just m, Just expr)
            else do
                return (r, Nothing, Nothing)

        , assert = function1 "assert"
        , sortDecl = \ns ->
            let
                dcHandler :: [DC] -> String
                dcHandler [] = ""
                dcHandler (DC n s:dc) =
                    let
                        si = map (\(s'', i) -> (s'', (selectorName (smt2 setup getmdl) s'') ++ show i)) $ zip s ([0..] :: [Integer])
                        s' = intercalate " " . map (\(_s, i) -> "(F_" ++ i ++ "_F " ++ (selectorName (smt2 setup getmdl) _s) ++ ")") $ si
                    in
                    "(" ++ n ++ " " ++ s' ++ ") " ++ dcHandler dc

                -- binders = intercalate " " $ concatMap (\(_, s, _) -> s) ns
                adtDecs = intercalate " " $ map (\(n, bn, _) -> "(" ++ n ++ " " ++ show (length bn) ++ ")") ns
            in
            if length ns > 0 then
                "(declare-datatypes (" ++ adtDecs ++ ") ("
                ++ (foldr (\(n, bn, dc) e -> 
                    "(par " ++ "(" ++ (intercalate " " bn) ++ ")" ++ " (" ++ (dcHandler dc) ++ ") )" ++ e) "" ns) ++  "))"
            else
                ""
            
        , varDecl = \n s -> "(declare-const " ++ n ++ " " ++ s ++ ")"
        
        , (.>=) = function2 ">="
        , (.>) = function2 ">"
        , (.=) = function2 "="
        , (./=) = \x -> function1 "not" . function2 "=" x
        , (.<=) = function2 "<="
        , (.<) = function2 "<"

        , (.&&) = function2 "and"
        , (.||) = function2 "or"
        , (.!) = function1 "not"
        , (.=>) = function2 "=>"
        , (.<=>) = function2 "="

        , (.+) = function2 "+"
        , (.-) = function2 "-"
        , (.*) = function2 "*"
        , (./) = function2 "/"
        , smtModulo = function2 "mod"
        , neg = function1 "-"

        , itor = function1 "to_real"

        , tester = \n e -> "(is-" ++ n ++ " " ++ e ++ ")"

        , ite = function3 "ite"

        , int = \x -> if x >= 0 then show x else "(- " ++ show (abs x) ++ ")"
        , float = \r -> 
            "(/ " ++ show (numerator r) ++ " " ++ show (denominator r) ++ ")"
        , double = \r ->
            "(/ " ++ show (numerator r) ++ " " ++ show (denominator r) ++ ")"
        , bool = \b -> if b then "true" else "false"
        , var = \n -> function1 n

        , sortInt = "Int"
        , sortFloat = "Real"
        , sortDouble = "Real"
        , sortBool = "Bool"
        , sortADT = \n ts -> if ts == [] then n else "(" ++ n ++ " " ++ (intercalate " " $ map (sortN (smt2 setup getmdl)) ts) ++ ")"

        , cons = \n asts s ->
            if asts /= [] then
                "(" ++ n ++ " " ++ (intercalate " " asts) ++ ")" 
            else
                n
        , varName = \n _ -> n

        , as = \ast s -> "(as " ++ ast ++ sortN (smt2 setup getmdl) s ++ ")"
    }

functionList :: String -> [String] -> String
functionList f xs = "(" ++ f ++ " " ++ (intercalate " " xs) ++ ")" 

function1 :: String -> String -> String
function1 f a = "(" ++ f ++ " " ++ a ++ ")"

function2 :: String -> String -> String -> String
function2 f a b = "(" ++ f ++ " " ++ a ++ " " ++ b ++ ")"

function3 :: String -> String -> String -> String -> String
function3 f a b c = "(" ++ f ++ " " ++ a ++ " " ++ b ++ " " ++ c ++ ")"

--TODO: SAME AS sortName in language, fix
sortN :: SMTConverter ast out io -> Sort -> ast
sortN smt SortInt = sortInt smt
sortN smt SortFloat = sortFloat smt
sortN smt SortDouble = sortDouble smt
sortN smt SortBool = sortBool smt
sortN smt (Sort n s) = sortADT smt n s

selectorName :: SMT2Converter -> Sort -> SMTName
selectorName smt SortInt = sortInt smt
selectorName smt SortFloat = sortFloat smt
selectorName smt SortDouble = sortDouble smt
selectorName smt SortBool = sortBool smt
selectorName _ (Sort n _) = n

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

getSMT :: Config -> IO (SMT2Converter, (Handle, Handle, ProcessHandle))
getSMT (Config {smt = Z3}) = do
    hpp <- getZ3ProcessHandles
    return (z3, hpp)
getSMT (Config {smt = CVC4}) = do
    hpp <- getCVC4ProcessHandles
    return (cvc4, hpp)

-- | getZ3ProcessHandles
-- This calls Z3, and get's it running in command line mode.  Then you can read/write on the
-- returned handles to interact with Z3
-- Ideally, this function should be called only once, and the same Handles should be used
-- in all future calls
getZ3ProcessHandles :: IO (Handle, Handle, ProcessHandle)
getZ3ProcessHandles = getProcessHandles $ proc "z3" ["-smt2", "-in"]

getCVC4ProcessHandles :: IO (Handle, Handle, ProcessHandle)
getCVC4ProcessHandles = do
    hhp@(h_in, h_out, pr) <- getProcessHandles $ proc "cvc4" ["--lang", "smt2.6", "--produce-models"]
    hPutStr h_in "(set-logic ALL_SUPPORTED)\n"

    return hhp

-- | setUpFormulaZ3
-- Writes a function to Z3
setUpFormulaZ3 :: Handle -> String -> IO ()
setUpFormulaZ3 h_in form = do
    hPutStr h_in "(reset)"
    hPutStr h_in form

setUpFormulaCVC4 :: Handle -> String -> IO ()
setUpFormulaCVC4 h_in form = do
    hPutStr h_in "(reset)"
    hPutStr h_in "(set-logic ALL_SUPPORTED)\n"
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
parseToSMTAST headers str s = correctTypes s . modifyFix elimLets . parseGetValues $ str
    where
        correctTypes :: Sort -> SMTAST -> SMTAST
        correctTypes (SortFloat) (VDouble r) = VFloat r
        correctTypes (SortDouble) (VFloat r) = VDouble r
        correctTypes _ (Cons "true" _ _) = VBool True
        correctTypes _ (Cons "false" _ _) = VBool False
        correctTypes _ c@(Cons _ _ _) = correctConsTypes c
        correctTypes _ a = a

        correctConsTypes :: SMTAST -> SMTAST
        correctConsTypes (Cons n smts (Sort _ _)) =
            let
                sName = M.lookup n consNameToSort
            in
            case sName of
                Just n' -> Cons n (map (uncurry correctTypes) (zip (repeat SortFloat) smts)) n' -- TODO : Fix SortFloat to be correct here...
                Nothing -> error ("Sort constructor " ++ (show n) ++ " not found in correctConsTypes\n\n" ++ str)
        correctConsTypes err = error $ "correctConsTypes: invalid SMTAST: " ++ show err

        consNameToSort :: M.Map SMTName Sort
        consNameToSort = 
            let
                nameDC = concat [x | (SortDecl x) <- headers]
            in
            M.fromList $ concatMap (\(n, _, dcs) -> [(dcn, Sort n []) | (DC dcn _) <- dcs]) nameDC

        elimLets :: SMTAST -> SMTAST
        elimLets (SLet (n, a) a') = modifyFix (replaceLets n a) a'
        elimLets a = a

        replaceLets :: SMTName -> SMTAST -> SMTAST -> SMTAST
        replaceLets n a c@(Cons n' _ _) = if n == n' then a else c
        replaceLets _ _ a = a

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

solveExpr :: Handle -> Handle -> SMT2Converter -> [SMTHeader] -> ExprEnv -> Expr -> IO Expr
solveExpr h_in h_out con headers eenv e = do
    let vs = symbVars eenv e
    vs' <- solveExpr' h_in h_out con headers vs
    let vs'' = map smtastToExpr vs'
    
    return $ foldr (uncurry replaceASTs) e (zip vs vs'')

solveExpr'  :: Handle -> Handle -> SMT2Converter -> [SMTHeader] -> [Expr] -> IO [SMTAST]
solveExpr' _ _ _ _ [] = return []
solveExpr' h_in h_out con headers (v:vs) = do
    v' <- solveExpr'' h_in h_out con headers v
    vs' <- solveExpr' h_in h_out con headers vs
    return (v':vs')

solveExpr'' :: Handle -> Handle -> SMT2Converter -> [SMTHeader] -> Expr -> IO SMTAST
solveExpr'' h_in h_out con headers e = do
    let smt = toSolverAST con $ exprToSMT e
    hPutStr h_in ("(eval " ++ smt ++ " :completion)\n")
    out <- getLinesMatchParens h_out
    _ <- evaluate (length out)

    return $ parseToSMTAST headers out (typeToSMT . typeOf $ e)
