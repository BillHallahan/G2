{-# LANGUAGE BangPatterns, FlexibleContexts, OverloadedStrings #-}

module Main (main) where

import G2.Config
import G2.Execution.PrimitiveEval
import G2.Initialization.MkCurrExpr
import G2.Interface
import G2.Language as G2 hiding (Handle)
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.KnownValues as KV
import G2.Language.Monad
import qualified G2.Language.TyVarEnv as TV
import G2.Lib.Printers
import G2.Solver.Converters
import G2.Solver.SMT2
import G2.Translation

import qualified Sygus.LexSygus as Sy
import qualified Sygus.ParseSygus as Sy
import Sygus.Syntax
import Sygus.Print

import Control.Exception.Base (evaluate)
import qualified Control.Monad.State as SM
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

    _ <- genSMTFunc [] src f Nothing config
    return ()

-------------------------------------------------------------------------------
-- CEGIS Loop
-------------------------------------------------------------------------------

-- | Use a CEGIS loop to generate an SMT conversion of a function
genSMTFunc :: [[ExecRes ()]] -- ^ Generated states 
           -> FilePath -- ^ Filepath containing function
           -> T.Text -- ^ Function name
           -> Maybe (Id, String) -- ^ Possible (SyGuS generated) function definition, along with the Id of the function being generated
           -> Config
           -> IO String
genSMTFunc constraints src f smt_def config = do
    (entry_f@(Id _ f_ty), ers, ng) <- runFunc src f smt_def config
    case ers of
        [] | Just (_, smt_def') <- smt_def -> return smt_def'
           | otherwise -> error "genSMTFunc: no SMT function generated" 
        (er:_) -> do
            let (varred_form, is, ng') = replaceLitsWithVars ng (conc_out er)
                lit_ers = transpose $ map execResCollectLits ers
            let new_constraints = zipWithDef (++) lit_ers constraints
                is_constraints = zip is new_constraints

            let pg = mkPrettyGuide is
            new_pieces <- mapM (\(i, constraints_) -> do
                                    smt_cmd <- runSygus constraints_
                                    print smt_cmd
                                    case smt_cmd of
                                        Just (DefineFun _ vars _ t) -> do
                                            let new_smt_def_ = sygusToHaskell "spec" (known_values $ final_state er) f_ty vars t
                                            putStrLn new_smt_def_
                                            return $ "!" ++ T.unpack (printName pg (idName i)) ++ " = (" ++ new_smt_def_ ++ ")"
                                        _ -> error "genSMTFunc: no SMT function generated")
                              is_constraints
            let vs = zipWith const (varList "z") (conc_args er)
                new_smt_def = "spec " ++ intercalate " " vs
                           ++ " = let " ++ intercalate "; " new_pieces ++ " in "
                           ++ T.unpack (printHaskellPG pg (final_state er) varred_form)
            genSMTFunc new_constraints src f (Just (entry_f, new_smt_def)) config

groupNonAdj :: (a -> a -> Bool) -> [a] -> [[a]]
groupNonAdj _ [] = []
groupNonAdj p (x:xs) = let (g, n) = partition (p x) xs in (x:g):groupNonAdj p n

zipWithDef :: (a -> a -> a) -> [a] -> [a] -> [a]
zipWithDef _ [] [] = []
zipWithDef _ xs [] = xs
zipWithDef _ [] ys = ys
zipWithDef f (x:xs) (y:ys) = f x y:zipWithDef f xs ys

isString :: Expr -> Bool
isString (App (Data dc) (Type (TyCon n _)))
    | nameOcc (dcName dc) == "[]"
    , nameOcc n == "Char" = True
isString (App (App (App (Data dc) _) _) _)
    | nameOcc (dcName dc) == ":" = True
isString _ = False

-- | Check that two Expr's are equal, disregarding specific values of (1) literals and (2) strings.
equalStruct :: Expr -> Expr -> Bool
equalStruct e1 e2 = modify repLit e1 == modify repLit e2
    where
        -- Replaces all literal values/concrete strings with "default" values
        repLit (Lit l) = Lit $ rep l
        repLit e | isString e = Var (Id (Name "!!__G2__!!_STRING" Nothing 0 Nothing) TyUnknown)
                 | otherwise = e

        rep (LitInt _) = LitInt 0
        rep (LitWord _) = LitWord 0
        rep (LitFloat _) = LitFloat 0
        rep (LitDouble _) = LitDouble 0
        rep (LitRational _) = LitRational 0
        rep (LitBV _) = LitBV []
        rep (LitChar _) = LitChar 'a'
        rep (LitString _) = LitString ""
        rep (LitInteger _) = LitInteger 0

modifyLits :: Monad m => (Expr -> m Expr) -> Expr -> m Expr
modifyLits f e@(Lit _) = f e
modifyLits f e | isString e = f e
               | Data dc <- e
               , nameOcc (dc_name dc) == "True" || nameOcc (dc_name dc) == "False" = f e
               | otherwise = modifyChildrenM (modifyLits f) e

-- | Return the passed expression, but with all literals replaced with fresh symbolic variables
replaceLitsWithVars :: NameGen -> Expr -> ( Expr
                                          , [Id] -- ^ The introduced variables
                                          , NameGen
                                          )
replaceLitsWithVars ng e =
    let ((e', ng'), xs) = SM.runState (runNamingT (modifyLits rep e) ng) [] in
    (e', xs, ng')
    where
        rep l = do
            x <- freshSeededStringN "x"
            let i = Id x $ typeOf TV.empty l
            SM.lift $ SM.modify (i:)
            return $ Var i

execResCollectLits :: ExecRes t -> [ExecRes t]
execResCollectLits er@(ExecRes { final_state = s }) =
    let
        e = conc_out er
        ls = collectLits e
    in
    map (\l -> er { final_state = s { curr_expr = CurrExpr Evaluate l }, conc_out = l }) ls

-- | Return all literals in the expression.
collectLits :: Expr -> [Expr]
collectLits e = SM.execState (modifyLits rep e) [] 
    where
        rep l = do
            SM.modify (l:)
            return l


-- foldLits :: (a -> G2.Lit -> a) -> a -> Expr -> a
-- foldLits _ x (Var _) = x
-- foldLits f x (Lit l) = f x l
-- foldLits _ x (Prim _ _) = x
-- foldLits _ x (Data _) = x
-- foldLits f x (App e1 e2) = foldLits f (foldLits f x e2) e1
-- foldLits f x (Lam _ _ e) = foldLits f x e
-- foldLits f x (Let b e) = foldr f (foldLits f x e) (map snd b)
-- foldLits

-------------------------------------------------------------------------------
-- Calling G2
-------------------------------------------------------------------------------

runFunc :: FilePath -- ^ Filepath containing function
        -> T.Text -- ^ Function name
        -> Maybe (Id, String) -- ^ Possible (SyGuS generated) function definition, along with the Id of the function being generated
        -> Config
        -> IO (Id, [ExecRes ()], NameGen)
runFunc src f smt_def config = do
    withSystemTempFile "SpecTemp.hs" (\temp handle -> do
        setUpSpec handle smt_def

        let config' = config { base = base config ++ [temp], maxOutputs = Just 10}

        proj <- guessProj (includePaths config') src

        (init_state, entry_f, bindings, mb_modname) <- initialStateFromFile proj [src]
                                        Nothing False f (mkCurrExpr TV.empty Nothing Nothing) (mkArgTys TV.empty)
                                        simplTranslationConfig config'
        
        let (comp_state, bindings') = if isJust smt_def then findInconsistent init_state bindings else (init_state, bindings)
        -- let config'' = if isJust smt_def then config' { logStates = Log Pretty "a_smt"} else config'
        T.putStrLn $ printHaskellPG (mkPrettyGuide $ getExpr comp_state) comp_state (getExpr comp_state)

        (er, b, to) <- runG2WithConfig proj [src] entry_f f [] mb_modname comp_state config' bindings'

        return (entry_f, er, name_gen bindings)
        )

setUpSpec :: Handle -> Maybe (Id, String) -> IO ()
setUpSpec h Nothing = hClose h
setUpSpec h (Just (Id _ t, spec)) = do
    let contents = "{-# LANGUAGE BangPatterns, MagicHash#-}\nmodule Spec where\nimport GHC.Prim2\n"
                    ++ "spec :: " ++ T.unpack (mkTypeHaskell t) ++ "\n"
                    ++ spec
    putStrLn contents
    hPutStrLn h contents
    hFlush h
    hClose h

-- | Find inputs that violate a found SMT definition
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
    let 

    let grm = GrammarDef pre_dec gram_defs'

    (h_in, h_out, _) <- getCVC5Sygus 60
    T.hPutStrLn h_in $ printSygus (SetLogic "ALL")
    T.putStrLn $ printSygus (SetLogic "ALL")
    let synthFun = SynthFun "spec" arg_vars ret_sort (Just grm)
    T.hPutStrLn h_in $ printSygus synthFun
    T.putStrLn $ printSygus synthFun
    mapM (execResToConstraints h_in) er
    T.hPutStrLn h_in $ printSygus CheckSynth
    T.putStrLn $ printSygus CheckSynth
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

        intSort = IdentSort (ISymb "Int")
        strSort = IdentSort (ISymb "String")
        boolSort = IdentSort (ISymb "Bool")

        args_sort = map (typeToSort kv . typeOf (tyvar_env s)) args
        arg_vars = map (uncurry SortedVar) $ zip (varList "z") args_sort
        ret_sort = typeToSort kv $ typeOf (tyvar_env s) out_e

        intIdent = BfIdentifier (ISymb "IntPr")
        strIdent = BfIdentifier (ISymb "StrPr")
        boolIdent = BfIdentifier (ISymb "BoolPr")

        -------------------------------
        -- Grammar
        -------------------------------
        grmString = [ GVariable strSort
                    , GBfTerm (BfIdentifierBfs (ISymb "str.++") [ strIdent, strIdent])
                    , GBfTerm (BfIdentifierBfs (ISymb "str.replace") [ strIdent, strIdent, strIdent])
                    ]
        grmInt = [ GVariable intSort
                 , GBfTerm (BfLiteral (LitNum 0))
                 , GBfTerm (BfLiteral (LitNum (-1)))
                 , GBfTerm (BfIdentifierBfs (ISymb "str.indexof") [ strIdent, strIdent, intIdent ])
                 , GBfTerm (BfIdentifierBfs (ISymb "str.len") [ strIdent ])
                 , GBfTerm (BfIdentifierBfs (ISymb "+") [ intIdent, intIdent])
                 ]
        grmBool = [ GBfTerm (BfIdentifierBfs (ISymb "str.prefixof") [ strIdent, strIdent ])
                  , GBfTerm (BfIdentifierBfs (ISymb "str.suffixof") [ strIdent, strIdent ])
                  , GBfTerm (BfIdentifierBfs (ISymb "=") [ strIdent, strIdent ])
                  , GBfTerm (BfIdentifierBfs (ISymb "=") [ intIdent, intIdent ])
                  ]


        gram_defs = [ GroupedRuleList "StrPr" strSort grmString
                    , GroupedRuleList "IntPr" intSort grmInt
                    , GroupedRuleList "BoolPr" boolSort grmBool]
        find_start_gram = findElem (\(GroupedRuleList _ sort _) -> sort == ret_sort) gram_defs
        gram_defs' = case find_start_gram of
                            Just (start_sym, other_sym) -> start_sym:other_sym
                            Nothing -> error "runSygus: no start symbol"
        pre_dec = map (\(GroupedRuleList n sort _) -> SortedVar n sort) gram_defs'

findElem       :: (a -> Bool) -> [a] -> Maybe (a, [a])
findElem p     = find' id
    where
      find' _ []         = Nothing
      find' prefix (x : xs)
          | p x          = Just (x, prefix xs)
          | otherwise    = find' (prefix . (x:)) xs

varList :: String -> [String]
varList x = map ((++) x . show) [1 :: Integer ..]

getCVC5Sygus :: Int -> IO (Handle, Handle, ProcessHandle)
getCVC5Sygus time_out = getProcessHandles $ proc "cvc5" ["--lang", "sygus", "--no-sygus-pbe", "--tlimit-per=" ++ show time_out]

parseSygus :: String -> [Cmd]
parseSygus = Sy.parse . Sy.lexSygus

execResToConstraints :: Handle -> ExecRes t -> IO ()
execResToConstraints h_in (ExecRes { final_state = s, conc_args = args, conc_out = out_e }) =
    let
        kv = known_values s

        call = TermCall (ISymb "spec") (map (exprToTerm kv) args)
        out_t = exprToTerm kv out_e
        cons = Constraint $ TermCall (ISymb "=") [call, out_t]
    in do
    T.hPutStrLn h_in $ printSygus cons
    T.putStrLn $ printSygus cons

exprToTerm :: KnownValues -> Expr -> Term
exprToTerm _ (Lit (LitInt x)) = TermLit (LitNum x)
exprToTerm kv dc | dc == mkTrue kv = TermLit (LitBool True)
                 | dc == mkFalse kv = TermLit (LitBool False)
exprToTerm _ e | Just s <- toString e = TermLit (LitStr s)
exprToTerm _ e = error $ "exprToTerm: unsupported Expr" ++ "\n" ++ show e

typeToSort :: KnownValues -> Type -> Sort
typeToSort kv t | t == TyLitInt = IdentSort (ISymb "Int")
typeToSort kv t | t == tyBool kv = IdentSort (ISymb "Bool")
typeToSort kv (TyApp t _) | t == tyList kv = IdentSort (ISymb "String")
typeToSort _ s = error $ "typeToSort: unsupported Type" ++ "\n" ++ show s

-------------------------------------------------------------------------------
-- Turning a SyGuS solution into Haskell code
-------------------------------------------------------------------------------
sygusToHaskell :: String -- ^ Binding name
               -> KnownValues
               -> Type
               -> [SortedVar]
               -> Term
               -> String
sygusToHaskell bn kv ty vars term =
    let
        -- binding = bn ++ " " ++ intercalate " " (map (\(SortedVar n _) -> n) vars) ++ " = "
        body = termToHaskell term
    in
    body

termToHaskell :: Term -> String
termToHaskell t =
    let
        (r, bind_p) = snd $ go 1 t
        binds = intercalate "; " bind_p
    in
    "let " ++ binds ++ " in " ++ r
    where
        mapGo :: Int -> [Term] -> (Int, [String], [String])
        mapGo x ts =
            let
                (x', rs_bs) = mapAccumL go x $ ts
                (rs, bs) = unzip rs_bs
            in
            (x', rs, concat bs)

        go :: Int
           -> Term
           -> ( Int
              , ( String -- ^ Final value to be returned
                , [String] -- ^ Let value pieces
                )
              )
        go !x (TermIdent (ISymb s)) = (x, (s, []))
        go !x (TermCall (ISymb f) ts) =
            let
                (x', vl_args, arg_binds) = mapGo x ts
                vars = intercalate " " vl_args
            in
            (x' + 1, ("y" ++ show x', arg_binds ++ ["!y" ++ show x' ++ " = " ++ smtFuncToPrim f ++ " " ++ vars]))
        go !x (TermLet ls t) =
            let
                (x', tss) = mapAccumL (\x_ (VarBinding n t) -> let (x_', (tc, ts)) = go x_ t in (x_', ts ++ ["!" ++ n ++ " = " ++ tc])) x ls
                (x'', (r, tss')) = go x' t
            in
            (x'', (r, concat tss ++ tss'))
        go !x (TermLit l) = (x, (goLit l, []))
        go !_ t = error $ "termToHaskell: unsupported term" ++ "\n" ++ show t

        goLit (LitStr s) = "\"" ++ s ++ "\""
        goLit (LitNum i) = show i
        goLit _ = error "termToHaskell: unsupported lit"

smtFuncToPrim :: String -> String
smtFuncToPrim "str.++" = "strAppend#"
smtFuncToPrim "str.indexof" = "strIndexOf#"
smtFuncToPrim "str.len" = "strLen#"
smtFuncToPrim "str.prefixof" = "strPrefixOf#"
smtFuncToPrim "str.replace" = "strReplace#"
smtFuncToPrim "str.suffixof" = "strSuffixOf#"
smtFuncToPrim "=" = "strEq#"
smtFuncToPrim f = error $ "smtFuncToPrim: unsupported " ++ f

-- | If an argument is a value that we need to wrap in a constructor, do so.
wrapArg :: KnownValues -> Type -> String -> String
wrapArg kv t s | Just w <- wrap kv t = "(" ++ w ++ " " ++ s ++ ")"
               | otherwise = s
                  
-- | If a return value is a type that we need to wrap in a constructor, do so.
wrapReturn :: KnownValues -> Type -> String -> String
wrapReturn kv t s | Just w <- wrap kv t = w ++ " (" ++ s ++ ")"
                  | otherwise = s

wrap :: KnownValues -> Type -> Maybe String
wrap kv t | t == tyInt kv = Just "I#"
          | otherwise = Nothing