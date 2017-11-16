-- | This defines an SMTConverter for the SMT2 language
-- It provides methods to construct formulas, as well as feed them to an external solver
module G2.Internals.SMT.SMT2 where

import G2.Internals.Language.Expr
import G2.Internals.Language.Support hiding (Model)
import G2.Internals.Language.Syntax hiding (Assert)
import G2.Internals.Language.Typing
import G2.Internals.SMT.Language
import G2.Internals.SMT.ParseSMT
import G2.Internals.SMT.Converters --It would be nice to not import this...

import Control.Exception.Base (evaluate)
import Data.List
import Data.List.Utils (countElem)
import qualified Data.Map as M
import Data.Ratio
import System.IO
import System.Process

type SMT2Converter = SMTConverter String String (Handle, Handle, ProcessHandle)

smt2 :: SMT2Converter
smt2 = SMTConverter {
          empty = ""  
        , merge = (++)

        , checkSat = \(h_in, h_out, _) formula -> do
            putStrLn "\n\n checkSat"
            putStrLn formula
            
            setUpFormula h_in formula
            r <- checkSat' h_in h_out

            putStrLn $ show r

            return r

        , checkSatGetModel = \(h_in, h_out, _) formula headers vs -> do
            setUpFormula h_in formula
            putStrLn "\n\n checkSatGetModel"
            putStrLn formula
            r <- checkSat' h_in h_out
            putStrLn $ "r =  " ++ show r
            if r == SAT then do
                mdl <- getModel h_in h_out vs
                -- putStrLn "======"
                -- putStrLn formula
                -- putStrLn ""
                -- putStrLn (show mdl)
                -- putStrLn "======"
                let m = parseModel headers mdl
                return (r, Just m)
            else do
                return (r, Nothing)

        , checkSatGetModelGetExpr = \(h_in, h_out, _) formula headers vs eenv (CurrExpr _ e) -> do
            setUpFormula h_in formula
            putStrLn "\n\n checkSatGetModelGetExpr"
            putStrLn formula
            r <- checkSat' h_in h_out
            putStrLn $ "r =  " ++ show r
            if r == SAT then do
                mdl <- getModel h_in h_out vs
                -- putStrLn "======"
                -- putStrLn formula
                -- putStrLn ""
                -- putStrLn (show mdl)
                -- putStrLn "======"
                let m = parseModel headers mdl

                expr <- solveExpr h_in h_out smt2 headers eenv e
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
                        si = map (\(s'', i) -> (s'', (selectorName s'') ++ show i)) $ zip s ([0..] :: [Integer])
                        s' = intercalate " " . map (\(_s, i) -> "(F_" ++ i ++ "_F " ++ (selectorName _s) ++ ")") $ si
                    in
                    "(" ++ n ++ " " ++ s' ++ ") " ++ dcHandler dc

                binders = intercalate " " $ concatMap (\(_, s, _) -> s) ns
            in
            "(declare-datatypes (" ++ binders ++ ") ("
            ++ (foldr (\(n, _, dc) e -> 
                "(" ++ n ++ " " ++ (dcHandler dc) ++ ") " ++ e) "" ns) ++  "))"
            
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

        , (.+) = function2 "+"
        , (.-) = function2 "-"
        , (.*) = function2 "*"
        , (./) = function2 "/"
        , neg = function1 "-"

        , tester = \n e -> "(is-" ++ n ++ " " ++ e ++ ")"

        , ite = function3 "ite"

        , int = show
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
        , sortADT = \n ts -> if ts == [] then n else "(" ++ n ++ " " ++ (intercalate " " $ map sortN ts) ++ ")"

        , cons = \n asts _ ->
            if asts /= [] then
                "(" ++ n ++ " " ++ (intercalate " " asts) ++ ")" 
            else
                n
        , varName = \n _ -> n
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
sortN :: Sort -> String
sortN SortInt = sortInt smt2
sortN SortFloat = sortFloat smt2
sortN SortDouble = sortDouble smt2
sortN SortBool = sortBool smt2
sortN (Sort n s) = sortADT smt2 n s

selectorName :: Sort -> String
selectorName SortInt = sortInt smt2
selectorName SortFloat = sortFloat smt2
selectorName SortDouble = sortDouble smt2
selectorName SortBool = sortBool smt2
selectorName (Sort n _) = n

-- | getZ3ProcessHandles
-- This calls Z3, and get's it running in command line mode.  Then you can read/write on the
-- returned handles to interact with Z3
-- Ideally, this function should be called only once, and the same Handles should be used
-- in all future calls
getZ3ProcessHandles :: IO (Handle, Handle, ProcessHandle)
getZ3ProcessHandles = do
    (m_h_in, m_h_out, _, p) <- createProcess (proc "z3" ["-smt2", "-in"])
        { std_in = CreatePipe, std_out = CreatePipe }

    let (h_in, h_out) =
            case (m_h_in, m_h_out) of
                (Just i, Just o) -> (i, o)
                _ -> error "Pipes to shell not successfully created."

    hSetBuffering h_in LineBuffering

    return (h_in, h_out, p)

-- | setUpFormula
-- Writes a function to Z3
setUpFormula :: Handle -> String -> IO ()
setUpFormula h_in form = do
    hPutStr h_in "(reset)"
    hPutStr h_in form

-- Checks if a formula, previously written by setUp formula, is SAT
checkSat' :: Handle -> Handle -> IO Result
checkSat' h_in h_out = do
    hPutStr h_in "(check-sat)\n"

    r <- hWaitForInput h_out (-1)
    if r then do
        out <- hGetLine h_out
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
parseToSMTAST headers str s = correctTypes s . modifyFix elimLets . parseSMT $ str
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

getModel :: Handle -> Handle -> [(SMTName, Sort)] -> IO [(SMTName, String, Sort)]
getModel h_in h_out ns = do
    hPutStr h_in "(set-option :model_evaluator.completion true)\n"
    getModel' ns
    where
        getModel' :: [(SMTName, Sort)] -> IO [(SMTName, String, Sort)]
        getModel' [] = return []
        getModel' ((n, s):nss) = do
            hPutStr h_in ("(eval " ++ n ++ " :completion)\n")
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
