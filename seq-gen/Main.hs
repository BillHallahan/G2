module Main where

import G2.Config
import G2.Execution.PrimitiveEval
import G2.Initialization.MkCurrExpr
import G2.Interface
import G2.Language hiding (Handle)
import qualified G2.Language.TyVarEnv as TV
import G2.Solver.SMT2
import G2.Translation

import qualified Sygus.LexSygus as Sy
import qualified Sygus.ParseSygus as Sy
import Sygus.Syntax
import Sygus.Print

import Control.Exception.Base (evaluate)
import Data.List
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.IO
import System.Process

main :: IO ()
main = do
    (src, entry, _, _, config) <- getConfig
    let f = T.pack entry

    er <- runFunc src f config
    putStrLn "HERE"
    smt_cmd <- runSygus er
    print smt_cmd
    case smt_cmd of
        Just (DefineFun _ vars _ t) -> putStrLn $ sygusToHaskell vars t
        _ -> return ()

runFunc :: FilePath -> T.Text -> Config -> IO [ExecRes ()]
runFunc src f config = do
    proj <- guessProj (includePaths config) src

    (init_state, entry_f, bindings, mb_modname) <- initialStateFromFile proj [src]
                                    Nothing False f (mkCurrExpr TV.empty Nothing Nothing) (mkArgTys TV.empty)
                                    simplTranslationConfig config

    (er, b, to) <- runG2WithConfig proj [src] entry_f f [] mb_modname init_state config bindings

    return er

runSygus :: [ExecRes t] -> IO (Maybe SmtCmd)
runSygus [] = return Nothing
runSygus er@(ExecRes { final_state = s, conc_args = args, conc_out = out_e}:_) = do
    -- let grmString = [ GBfTerm (BfIdentifierBfs (ISymb "str.++") [ strIdent, strIdent])
    --                 , GBfTerm (BfIdentifierBfs (ISymb "str.replace") [ strIdent, strIdent, strIdent]) ]
    --     grmInt = [ GBfTerm (BfIdentifierBfs (ISymb "str.len") [ strIdent ])
    --              , GBfTerm (BfIdentifierBfs (ISymb "+") [ intIdent, intIdent]) ]

    -- let grm =
    --         GrammarDef [SortedVar "StrPr" stringSort, SortedVar "IntPr" intSort]
    --             [ GroupedRuleList "StrPr" stringSort grmString
    --             , GroupedRuleList "IntPr" intSort grmInt]
    (h_in, h_out, _) <- getCVC5Sygus 60
    T.hPutStrLn h_in $ printSygus (SetLogic "ALL")
    let synthFun = SynthFun "spec" arg_vars ret_sort Nothing -- (Just grm)
    T.hPutStrLn h_in $ printSygus synthFun
    mapM (execResToConstraints h_in) er
    T.hPutStrLn h_in $ printSygus CheckSynth
    _ <- hWaitForInput h_out 70
    out <- getLinesMatchParens h_out
    -- putStrLn $ "Z3 out: " ++ out
    _ <- evaluate (length out)
    putStrLn out
    -- We get back something of the form:
    --  ((define-fun ... ))
    -- The parseSygus function does not like having the extra "("/")" at the beginning/end-
    -- so we drop them.
    let sy_out = parseSygus . tail . init $ out
    case sy_out of
        [SmtCmd def_fun] -> return $ Just def_fun
        _ -> return Nothing
    where
        kv = known_values s

        -- intSort = IdentSort (ISymb "Int")
        args_sort = map (typeToSort kv . typeOf (tyvar_env s)) args
        arg_vars = map (uncurry SortedVar) $ zip (varList "x") args_sort
        ret_sort = typeToSort kv $ typeOf (tyvar_env s) out_e

    --     intIdent = BfIdentifier (ISymb "IntPr")
    --     strIdent = BfIdentifier (ISymb "StrPr")

varList :: String -> [String]
varList x = map ((++) x . show) [1 :: Integer ..]

getCVC5Sygus :: Int -> IO (Handle, Handle, ProcessHandle)
getCVC5Sygus time_out = getProcessHandles $ proc "cvc5" ["--lang", "sygus", "--tlimit-per=" ++ show time_out]

parseSygus :: String -> [Cmd]
parseSygus = Sy.parse . Sy.lexSygus

execResToConstraints :: Handle -> ExecRes t -> IO ()
execResToConstraints h_in (ExecRes { final_state = s, conc_args = args, conc_out = out_e }) =
    let
        kv = known_values s

        call = TermCall (ISymb "spec") (map (exprToTerm kv) args)
        out_t = exprToTerm kv out_e
        cons = Constraint $ TermCall (ISymb "=") [call, out_t]
    in
    T.hPutStrLn h_in $ printSygus cons

exprToTerm :: KnownValues -> Expr -> Term
exprToTerm _ (App (Data _) (Lit (LitInt x))) = TermLit (LitNum x)
exprToTerm _ e | Just s <- toString e = TermLit (LitStr s)
exprToTerm _ _ = error "exprToTerm: unsupported Expr"

typeToSort :: KnownValues -> Type -> Sort
typeToSort kv (TyApp t_list _) | t_list == tyList kv = IdentSort (ISymb "String")
typeToSort _ _ = error "typeToSort: unsupported Type"

sygusToHaskell :: [SortedVar] -> Term -> String
sygusToHaskell vars t =
    let
        header = "spec " ++ intercalate " " (map (\(SortedVar n _) -> n) vars) ++ " = "
        body = termToHaskell t
    in
    header ++ body

termToHaskell :: Term -> String
termToHaskell t =
    let
        (r, bind_p) = go t
        binds = intercalate "; " bind_p
    in
    "let " ++ binds ++ " in " ++ r
    where
        mapGo :: [Term] -> ([String], [String])
        mapGo ts =
            let (rs, bs) = unzip . map go $ ts in (rs, concat bs)

        go :: Term
           -> ( String -- ^ Final value to be returned
              , [String] -- ^ Let value pieces
              )
        go (TermIdent (ISymb s)) = (s, [])
        go (TermCall (ISymb "str.++") ts) =
            let
                (vl_args, arg_binds) = mapGo ts

                binds = map (\(v, ar) -> "!" ++ v ++ " = " ++ ar) $ zip (varList "y") vl_args
                vars = intercalate " " vl_args
            in
            ("strAppend#" ++ " " ++ vars, arg_binds ++ binds)
        go _ = error "termToHaskell: unsupported term"