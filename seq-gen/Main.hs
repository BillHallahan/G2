module Main where

import G2.Config
import G2.Initialization.MkCurrExpr
import G2.Interface
import G2.Language
import qualified G2.Language.TyVarEnv as TV
import G2.Translation

import Sygus.Syntax
import Sygus.Print

import qualified Data.Text as T
import qualified Data.Text.IO as T

main :: IO ()
main = do
    (src, entry, _, _, config) <- getConfig
    let f = T.pack entry

    er <- runFunc src f config
    putStrLn "HERE"
    runSygus er

runFunc :: FilePath -> T.Text -> Config -> IO [ExecRes ()]
runFunc src f config = do
    proj <- guessProj (includePaths config) src

    (init_state, entry_f, bindings, mb_modname) <- initialStateFromFile proj [src]
                                    Nothing False f (mkCurrExpr TV.empty Nothing Nothing) (mkArgTys TV.empty)
                                    simplTranslationConfig config

    (er, b, to) <- runG2WithConfig proj [src] entry_f f [] mb_modname init_state config bindings

    return er

runSygus :: [ExecRes t] -> IO ()
runSygus er = do    
    -- let grmString = [ GBfTerm (BfIdentifierBfs (ISymb "str.++") [ strIdent, strIdent])
    --                 , GBfTerm (BfIdentifierBfs (ISymb "str.replace") [ strIdent, strIdent, strIdent]) ]
    --     grmInt = [ GBfTerm (BfIdentifierBfs (ISymb "str.len") [ strIdent ])
    --              , GBfTerm (BfIdentifierBfs (ISymb "+") [ intIdent, intIdent]) ]

    -- let grm =
    --         GrammarDef [SortedVar "StrPr" stringSort, SortedVar "IntPr" intSort]
    --             [ GroupedRuleList "StrPr" stringSort grmString
    --             , GroupedRuleList "IntPr" intSort grmInt]
    let synthFun = SynthFun "spec" [] stringSort Nothing -- (Just grm)
    T.putStrLn $ printSygus synthFun
    mapM execResToConstraints er
    T.putStrLn $ printSygus CheckSynth
    where
        -- intSort = IdentSort (ISymb "Int")
        stringSort = IdentSort (ISymb "String")

    --     intIdent = BfIdentifier (ISymb "IntPr")
    --     strIdent = BfIdentifier (ISymb "StrPr")

execResToConstraints :: ExecRes t -> IO ()
execResToConstraints (ExecRes { final_state = s, conc_args = args, conc_out = out_e }) =
    let
        kv = known_values s

        call = TermCall (ISymb "spec") (map (exprToTerm kv) args)
        out_t = exprToTerm kv out_e
        cons = Constraint $ TermCall (ISymb "=") [call, out_t]
    in
    T.putStrLn $ printSygus cons

exprToTerm :: KnownValues -> Expr -> Term
exprToTerm _ (App (Data _) (Lit (LitInt x))) = TermLit (LitNum x)
exprToTerm _ _ = error "exprToTerm: unsupported Expr"