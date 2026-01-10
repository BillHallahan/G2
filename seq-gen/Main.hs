{-# LANGUAGE OverloadedStrings #-}

module Main where

import G2.Config
import G2.Execution.PrimitiveEval
import G2.Initialization.MkCurrExpr
import G2.Interface
import G2.Language hiding (Handle)
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.TyVarEnv as TV
import G2.Lib.Printers
import G2.Solver.SMT2
import G2.Translation

import qualified Sygus.LexSygus as Sy
import qualified Sygus.ParseSygus as Sy
import Sygus.Syntax
import Sygus.Print

import Control.Exception.Base (evaluate)
import qualified Data.HashMap.Lazy as HM
import Data.List
import Data.Maybe
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.IO
import System.IO.Temp
import System.Process

main :: IO ()
main = do
    (src, entry, _, _, config) <- getConfig
    let f = T.pack entry

    _ <- genSMTFunc src f Nothing config
    return ()

-- | Use a CEGIS loop to generate an SMT conversion of a function
genSMTFunc :: FilePath -- ^ Filepath containing function
           -> T.Text -- ^ Function name
           -> Maybe (Id, String) -- ^ Possible (SyGuS generated) function definition, along with the Id of the function being generated
           -> Config
           -> IO String
genSMTFunc src f smt_def config = do
    (entry_f, ers) <- runFunc src f smt_def config
    case null ers of
        True | Just (_, smt_def') <- smt_def -> return smt_def'
        _ -> do
            smt_cmd <- runSygus ers
            print smt_cmd
            case smt_cmd of
                Just (DefineFun _ vars _ t) -> do
                    let new_smt_def = sygusToHaskell vars t
                    putStrLn new_smt_def
                    genSMTFunc src f (Just (entry_f, new_smt_def)) config
                _ -> error "genSMTFunc: no SMT function generated"

runFunc :: FilePath -- ^ Filepath containing function
        -> T.Text -- ^ Function name
        -> Maybe (Id, String) -- ^ Possible (SyGuS generated) function definition, along with the Id of the function being generated
        -> Config
        -> IO (Id, [ExecRes ()])
runFunc src f smt_def config = do
    withSystemTempFile "SpecTemp.hs" (\temp handle -> do
        setUpSpec handle smt_def

        let config' = config { base = base config ++ [temp]}

        proj <- guessProj (includePaths config') src

        (init_state, entry_f, bindings, mb_modname) <- initialStateFromFile proj [src]
                                        Nothing False f (mkCurrExpr TV.empty Nothing Nothing) (mkArgTys TV.empty)
                                        simplTranslationConfig config'
        
        let (comp_state, bindings') = if isJust smt_def then findInconsistent init_state bindings else (init_state, bindings)
        -- let config'' = if isJust smt_def then config' { logStates = Log Pretty "a_smt"} else config'
        T.putStrLn $ printHaskellPG (mkPrettyGuide $ getExpr comp_state) comp_state (getExpr comp_state)

        (er, b, to) <- runG2WithConfig proj [src] entry_f f [] mb_modname comp_state config' bindings'

        return (entry_f, er)
        )

setUpSpec :: Handle -> Maybe (Id, String) -> IO ()
setUpSpec h Nothing = hClose h
setUpSpec h (Just (Id _ t, spec)) = do
    let contents = "{-# LANGUAGE MagicHash#-}\nmodule Spec where\nimport GHC.Prim2\n"
                    ++ "spec :: " ++ T.unpack (mkTypeHaskell t) ++ "\n"
                    ++ spec
    putStrLn contents
    hPutStrLn h contents
    hFlush h
    hClose h


findInconsistent :: State t -> Bindings -> (State t, Bindings)
findInconsistent s@(State { expr_env = eenv
                          , known_values = kv
                          , type_classes = tc
                          , tyvar_env = tv_env }) b@(Bindings { name_gen = ng })
    | Just (smt_def, e) <- E.lookupNameMod "spec" (Just "Spec") eenv =
    let
        
        app_smt_def = mkApp $ Var (Id smt_def (typeOf tv_env e)):map Var (inputIds s b)

        ret_type = returnType $ typeOf tv_env e
        m_eq_dict = typeClassInst tc HM.empty (KV.eqTC kv) ret_type
    in
    case m_eq_dict of
        Just eq_dict ->
            let
                (val_name, ng') = freshSeededString "val" ng
                (comp_name, ng'') = freshSeededString "comp" ng'

                comp_e = mkApp [Var (Id (KV.eqFunc kv) TyUnknown)
                              , Type ret_type
                              , eq_dict
                              , app_smt_def
                              , Var (Id val_name TyUnknown)]
                new_curr_expr = Let [ (Id val_name TyUnknown, getExpr s)
                                    , (Id comp_name TyUnknown, comp_e)
                                    ] $ Assert Nothing (Var (Id comp_name TyUnknown)) (Var (Id val_name TyUnknown))
            in
            ( s { curr_expr = CurrExpr Evaluate new_curr_expr, true_assert = False }
            , b { name_gen = ng'' })
        Nothing -> error $ "findInconsistent: no Eq dict" ++ show ret_type
    | otherwise = error $ "findInconsistent: spec not found"

-------------------------------------------------------------------------------
-- Calling/reading from SyGuS solver
-------------------------------------------------------------------------------
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

-------------------------------------------------------------------------------
-- Turning a SyGuS solution into Haskell code
-------------------------------------------------------------------------------
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