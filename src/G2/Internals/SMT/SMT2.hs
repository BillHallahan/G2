module G2.Internals.SMT.SMT2 where

import G2.Internals.Core.Language
import G2.Internals.SMT.Language
import G2.Internals.SMT.ParseSMT

import Control.Exception.Base (evaluate)
import Data.List
import qualified Data.Map as M
import Data.Ratio
import System.IO
import System.Process
import GHC.IO.Handle

type TypeDecl = String
type VarDecl = String
type ASTDecl = String

smt2 :: SMTConverter String String
smt2 = SMTConverter {
          empty = ""  
        , merge = (++)

        , checkSat = \formula -> do
            (h_in, h_out, p) <- setUpFormula formula
            r <- checkSat' h_in h_out
            hClose h_in
            hClose h_out
            terminateProcess p
            return r

        , checkSatAndGetModel = \formula vars -> do
            (h_in, h_out, p) <- setUpFormula formula
            r <- checkSat' h_in h_out
            if r == SAT then do
                model <- return =<< getModel h_in h_out vars
                putStrLn (show model)
                m <- return . parseModel $ model
                hClose h_in
                hClose h_out
                terminateProcess p
                return (r, Just m)
            else do
                hClose h_in
                hClose h_out
                terminateProcess p
                return (r, Nothing)

        , assert = function1 "assert"
        , sortDecl = \ns ->
            let
                --TODO : SAME AS sortName in langauage, fix
                sortN :: Sort -> String
                sortN SortInt = sortInt smt2
                sortN SortFloat = sortFloat smt2
                sortN SortDouble = sortDouble smt2
                sortN SortBool = sortBool smt2
                sortN (Sort n s) = sortADT smt2 n s

                dcHandler :: [DC] -> String
                dcHandler [] = ""
                dcHandler (DC n s:dc) =
                    let
                        si = map (\(_s, i) -> (_s, (sortN _s) ++ show i)) $ zip s [0..]
                        s' = intercalate " " . map (\(_s, i) -> "(_" ++ i ++ " " ++ (sortN _s) ++ ")") $ si
                    in
                    if s /= [] then
                        "(" ++ n ++ " " ++ s' ++ ") " ++ dcHandler dc
                    else
                        n ++ " " ++ dcHandler dc
            in
            "(declare-datatypes () ("
            ++ (foldr (\(n, dc) e -> 
                "(" ++ n ++ " " ++ (dcHandler dc) ++ ") " ++ e) "" ns) ++  "))"
        , varDecl = \n s -> "(declare-const " ++ n ++ " " ++ s ++ ")"
        
        , (.>=) = function2 ">="
        , (.>) = function2 ">"
        , (.=) = function2 "="
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
        , sortADT = \n _ -> n

        , cons = \n asts s ->
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

setUpFormula :: String -> IO (Handle, Handle, ProcessHandle)
setUpFormula form = do
    (m_h_in, m_h_out, _, p) <- createProcess (proc "z3" ["-smt2", "-in"]) { std_in = CreatePipe, std_out = CreatePipe }

    let (h_in, h_out) =
            case (m_h_in, m_h_out) of
                (Just i, Just o) -> (i, o)
                _ -> error "Pipes to shell not successfully created."

    hSetBuffering h_in LineBuffering

    hPutStr h_in form
    return (h_in, h_out, p)

checkSat' :: Handle -> Handle -> IO Result
checkSat' h_in h_out = do
    hPutStr h_in "(check-sat)\n"

    r <- hWaitForInput h_out 10000
    if r then do
        out <- hGetLine h_out
        evaluate (length out)

        if out == "sat" then
            return SAT
        else if out == "unsat" then
            return UNSAT
        else
            return Unknown
    else do
        return Unknown

parseModel :: [(Name, String)] -> Model
parseModel = foldr (\(n, s) -> M.insert n s) M.empty . map (\(n, s) -> (n, parseModel' s))
    where
        parseModel' :: String -> SMTAST
        parseModel' s = modifyFix elimLets $ parseSMT s

        elimLets :: SMTAST -> SMTAST
        elimLets (SLet (n, a) a') = modifyFix (replaceLets n a) a'
        elimLets a = a

        replaceLets :: Name -> SMTAST -> SMTAST -> SMTAST
        replaceLets n a c@(Cons n' _ _) = if n == n' then a else c
        replaceLets _ _ a = a

getModel :: Handle -> Handle -> [(Name, Sort)] -> IO [(Name, String)]
getModel h_in h_out ns = do
    hPutStr h_in "(set-option :model_evaluator.completion true)\n"
    getModel' h_in h_out ns
    where
        getModel' :: Handle -> Handle -> [(Name, Sort)] -> IO [(Name, String)]
        getModel' _ _ [] = return []
        getModel' h_in h_out ((n, s):ns) = do
            hPutStr h_in ("(eval " ++ n ++ " :completion)\n")
            out <- getLinesUntil h_out (not . isPrefixOf "(let")
            evaluate (length out)

            return . (:) (n, out) =<< getModel' h_in h_out ns

getLinesUntil :: Handle -> (String -> Bool) -> IO String
getLinesUntil h_out p = do
    out <- hGetLine h_out
    if p out then
        return out
    else
        return . (++) (out ++ "\n") =<< getLinesUntil h_out p