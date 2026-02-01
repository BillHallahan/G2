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
import G2.Solver.SMT2
import G2.Translation

import qualified Sygus.LexSygus as Sy
import qualified Sygus.ParseSygus as Sy
import Sygus.Syntax
import Sygus.Print

import Control.Exception (assert, evaluate)
import qualified Control.Monad.State as SM
import Data.Char
import qualified Data.HashMap.Lazy as HM
import Data.List
import Data.Maybe
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Options.Applicative
import System.Directory
import System.IO
import System.IO.Temp
import System.Process
import Data.Char (isAscii)

-------------------------------------------------------------------------------
-- Methodology
-------------------------------------------------------------------------------
-- If we have a Haskell function like:
-- @
-- f1 :: String -> String -> String -> String
-- f1 xs ys zs = xs ++ ys ++ zs
-- @
-- we give that to the symbolic executor, and get input/output pairs like:
-- @
-- f1 "A" "" "" = "A"
-- f1 "ABC" "D" "" = "ABCD"
-- @
-- We then give these to a SyGuS solver to automatically generate an SMT translation of the (observed) function behavior:
-- @
-- ((define-fun spec ((z1 String) (z2 String) (z3 String)) String (str.++ z1 z2)))
-- @
-- which can then be turned back into Haskell code:
-- @
-- spec z1 z2 z3 = let !x = (let !y1 = strAppend# z1 z2 in y1) in x
-- @
-- We then run the following in the symbolic executor, to look for input pairs on which f1 and spec return different outputs:
-- @
-- let
--       val = let
--             fs'4 = f1 fs'3 fs'2 fs in fs'4
--       comp = (spec fs'3 fs'2 fs) == val in assert (comp) (val)
-- @
-- (Note that we are looking for assertion VIOLATIONS, so places where `comp` returns False)
--
-- Here, we will find that val and comp differ on, for instance:
-- @ f1 "" "" ("A") = "A" @
-- and so we add this as an example for the synthesizer... and repeat until we get a correct SMT translation of the function:
-- @
-- spec z1 z2 z3 = let !x = (let !y1 = strAppend# z2 z3; !y2 = strAppend# z1 y1 in y2) in x
-- @
--
-- See also Note [Return patterns].

-- Note [Return patterns]
-- If a function has a non-string return type:
-- @ f :: String -> Maybe String @
-- We will likely get return values of both the "shape" `Nothing`, and the "shape" `Just s` (for some String s.)
-- However, the SyGuS solver can only handle Strings, not Maybes (or other ADTs). Thus, we group outputs with common
-- shapes, and synthesize both predicates to select which shape to return, and well as expressions to fill each string
-- (or other literal) value in each shape. For instance, for the function f we would form:
-- @
-- f_smt x = case p x of
--                 True -> Just (f_smt x)
--                 False -> Nothing
-- @
-- And then synthesize both a `p` and a `f_smt` function.
--
-- See the PatternRes type.


main :: IO ()
main = do
    (src, m_entry, config) <- getSeqGenConfig
    let config' = config { favor_chars = True }
    case m_entry of
        Just entry -> do
            let f = T.pack entry
            _ <- genSMTFunc [] [src] f Nothing config'
            return ()
        Nothing -> do
            cnt <- readFile src
            let lns = lines cnt
            mapM_ (run config') $ map T.pack lns
        where
            run con f = do
                let spl_f = T.splitOn "." f
                    f_name = last spl_f
                genSMTFunc [] [] f_name Nothing con

getSeqGenConfig :: IO (String, Maybe String, Config)
getSeqGenConfig = do
    homedir <- getHomeDirectory
    execParser (seqGenConfig homedir)

seqGenConfig :: String -> ParserInfo (String, Maybe String, Config)
seqGenConfig homedir =
    info (((,,)
                <$> argument str (metavar "FILE")
                <*> option (eitherReader (Right . Just))
                   (long "function"
                   <> metavar "F"
                   <> value Nothing
                   <> help "a function to synthesize an SMT definition for")
                <*> mkConfig homedir) <**> helper)
          ( fullDesc
          <> progDesc "Synthesis of equivalent SMT definitions"
          <> header "The G2 Synthesizer" )

-------------------------------------------------------------------------------
-- CEGIS Loop
-------------------------------------------------------------------------------

-- | A `PatternRes`(ult) is a particular "shape" of expression that we are returning from a function.
-- A single pattern might involve multiple literal values, each of which we can individually synthesize a
-- specification for.  For example:
-- * a tuple `(x, y) :: (String, String)` would need a string expression to be synthesized for both `x` and `y`.
-- * a function returning `Maybe String` would (likely) have two patterns, one for the case where we return
-- `Just s` (for some String s) and one for the case where we return `Nothing`.
-- See Note [Return patterns]
data PatternRes = PL { pattern :: Expr, lit_expr :: Expr, pat_ids :: [Id], orig_exec_res :: [ExecRes ()], lit_vals :: [[ExecRes ()]] }

mergePatternRes :: PatternRes -> PatternRes -> PatternRes
mergePatternRes pl@(PL { lit_expr = le1, lit_vals = lv1 }) (PL { lit_expr = le2, lit_vals = lv2 }) =
    assert (eqIgnoringLits le1 le2)
    $ pl { lit_vals = zipWithDef (++) lv1 lv2 }

insertER :: NameGen -> ExecRes () -> [PatternRes] -> [PatternRes]
insertER ng er [] =
    let
        (varred_form, is, ng') = replaceLitsWithVars ng (conc_out er)
        lit_ers = execResCollectLits er
    in
    [PL { pattern = varred_form, lit_expr = conc_out er, pat_ids = is, orig_exec_res = [er], lit_vals = map (:[]) lit_ers }]
insertER ng er (pl:pls)
    | eqIgnoringLits (conc_out er) (lit_expr pl) =
        let
            lit_ers = execResCollectLits er
        in
        pl { orig_exec_res = er:orig_exec_res pl, lit_vals = zipWith (:) lit_ers (lit_vals pl) }:pls
    | otherwise = pl:insertER ng er pls

-- | Use a CEGIS loop to generate an SMT conversion of a function
genSMTFunc :: [PatternRes] -- ^ Generated states
           -> [FilePath] -- ^ Filepath containing function
           -> T.Text -- ^ Function name
           -> Maybe (Id, String) -- ^ Possible (SyGuS generated) function definition, along with the Id of the function being generated
           -> Config
           -> IO String
genSMTFunc pls src f smt_def config = do
    putStrLn "\n--- Running function --- "
    (entry_f, ers, ng) <- runFunc src f smt_def config
    case ers of
        [] | Just (_, smt_def') <- smt_def -> return smt_def'
           | otherwise -> error "genSMTFunc: no SMT function generated" 
        (er:_) -> do
            putStrLn "\n--- Synthesizing --- "
            let pls' = foldr (insertER ng) pls ers

            new_smt_piece <- formFunction (known_values . final_state $ er) pls'

            let vs = zipWith const argList (relArgs $ conc_args er)
                new_smt_def = "spec " ++ intercalate " " vs ++ " = " ++ new_smt_piece
            genSMTFunc pls' src f (Just (entry_f, new_smt_def)) config

formFunction :: KnownValues -> [PatternRes] -> IO String
formFunction _ [] = error "formFunction: empty list"
formFunction _ [pr] = solveOnePattern pr
formFunction kv (pr:prs) = do
    putStrLn "\n* Solving Branch Condition"
    br <- solveBranchConditions kv pr prs
    putStrLn "\n* Solving Pattern"
    r1 <- solveOnePattern pr
    r2 <- formFunction kv prs
    return $ "if " ++ br ++ " then " ++ r1 ++ " else " ++ r2

solveOnePattern :: PatternRes -> IO String
solveOnePattern (PL { pattern = varred_form, pat_ids = is, lit_vals = constraints@((er:_):_) }) = do
    let is_constraints = zip is constraints

    let pg = mkPrettyGuide is
    new_pieces <- mapM (\(i, constraints_) -> do
                            new_smt_def <- computeProdPieces constraints_
                            return $ "!" ++ T.unpack (printName pg (idName i)) ++ " = (" ++ new_smt_def ++ ")")
                        is_constraints
    let new_smt_def = "let " ++ intercalate "; " new_pieces ++ " in "
                    ++ T.unpack (toHaskellCode (Just $ final_state er) pg varred_form)
    return new_smt_def
solveOnePattern (PL { pattern = varred_form, pat_ids = is }) = do
    let pg = mkPrettyGuide is
    return . T.unpack $ toHaskellCode Nothing pg varred_form

toHaskellCode :: Maybe (State t) -> PrettyGuide -> Expr -> T.Text
toHaskellCode _ _ e | Prim Error _:_ <- unApp e = "error \"\""
toHaskellCode (Just s) pg e = printHaskellPG pg s e
toHaskellCode Nothing pg e = printHaskellDirtyPG pg e

solveBranchConditions :: KnownValues -> PatternRes -> [PatternRes] -> IO String
solveBranchConditions kv pr prs = do
    let true_lv = map (setBool True) (orig_exec_res pr)
        false_lv = map (setBool False) (concatMap orig_exec_res prs)
        pat_id = Id (Name "g2__BOOL_ID" Nothing 0 Nothing) TyUnknown
        bool_pr = pr { pattern = Var pat_id, pat_ids = [pat_id], lit_vals = [true_lv ++ false_lv] }
    solveOnePattern bool_pr
    where
        setBool b er = er { final_state = (final_state er) {curr_expr = CurrExpr Return (mkBool kv b)}, conc_out = mkBool kv b }


computeProdPieces :: [ExecRes t] -> IO String
computeProdPieces constraints = do
    smt_cmd <- synthFunc constraints
    print smt_cmd
    case smt_cmd of
        Just (DefineFun _ _ _ t) -> return $ termToHaskell t
        _ -> error "genSMTFunc: no SMT function generated"

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

-- | Check that two Expr's are equal, disregarding specific values of (1) literals, (2) strings, and (3) DC uniques.
eqIgnoringLits :: Expr -> Expr -> Bool
eqIgnoringLits e1 e2 =
    case modify repLit e1 `eqUpToTypes` modify repLit e2 of
        True -> True
        False -> False
    where
        -- Replaces all literal values/concrete strings with "default" values
        repLit (Lit l) = Lit $ rep l
        repLit (Data dc)
            | nameOcc (dc_name dc) == "True" || nameOcc (dc_name dc) == "False" = Var (Id (Name "!!__G2__!!_BOOL" Nothing 0 Nothing) TyUnknown)
            | otherwise = Data (dc { dc_name = Name (nameOcc (dc_name dc)) Nothing 0 Nothing})
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

-------------------------------------------------------------------------------
-- Calling G2
-------------------------------------------------------------------------------

runFunc :: [FilePath] -- ^ Filepath containing function
        -> T.Text -- ^ Function name
        -> Maybe (Id, String) -- ^ Possible (SyGuS generated) function definition, along with the Id of the function being generated
        -> Config
        -> IO (Id, [ExecRes ()], NameGen)
runFunc src f smt_def config = do
    withSystemTempFile "SpecTemp.hs" (\temp handle -> do
        setUpSpec handle smt_def

        let config' = config { base = base config ++ temp:src, maxOutputs = Just 10}

        proj <- case src of
                    src':_ -> guessProj (includePaths config') src'
                    _ -> return []

        (init_state, entry_f, bindings, mb_modname) <- initialStateFromFile proj src
                                        Nothing False f (mkCurrExpr TV.empty Nothing Nothing) (mkArgTys config' TV.empty)
                                        simplTranslationConfig config'
        
        let (comp_state, bindings') = if isJust smt_def then findInconsistent init_state bindings else (init_state, bindings)
        -- let config'' = if isJust smt_def then config' { logStates = Log Pretty "a_smt"} else config'
        T.putStrLn $ printHaskellPG (mkPrettyGuide $ getExpr comp_state) comp_state (getExpr comp_state)

        (er, b, to) <- runG2WithConfig proj src entry_f f [] mb_modname comp_state config' bindings'

        return (entry_f, er, name_gen bindings)
        )

setUpSpec :: Handle -> Maybe (Id, String) -> IO ()
setUpSpec h Nothing = hClose h
setUpSpec h (Just (Id _ t, spec)) = do
    let (_, t')= splitTyForAlls $ repAllTyVarsWithChar t
        contents = "{-# LANGUAGE BangPatterns, MagicHash, ScopedTypeVariables #-}\nmodule Spec where\nimport GHC.Prim2\n"
                    ++ "import Control.Exception\n"
                    ++ "import System.IO.Unsafe\n\n"
                    ++ "tryMaybe :: IO a -> IO (Maybe a)\n"
                    ++ "tryMaybe a = catch (a >>= \\v -> return (Just v)) (\\(e :: SomeException) -> return Nothing)\n\n"
                    ++ "tryMaybeUnsafe :: a -> Maybe a\n"
                    ++ "tryMaybeUnsafe x = unsafePerformIO $ tryMaybe (let !y = x in return y)\n\n"
                    ++ "spec :: " ++ T.unpack (mkTypeHaskell t') ++ "\n"
                    ++ spec
    putStrLn contents
    hPutStrLn h contents
    hFlush h
    hClose h
    where
        repAllTyVarsWithChar (TyVar _) = (TyCon (Name "Char" Nothing 0 Nothing) TYPE)
        repAllTyVarsWithChar t_ = modifyChildren repAllTyVarsWithChar t_

-- | Find inputs that violate a found SMT definition
findInconsistent :: State t -> Bindings -> (State t, Bindings)
findInconsistent s@(State { expr_env = eenv
                          , known_values = kv
                          , type_classes = tc
                          , tyvar_env = tv_env }) b@(Bindings { name_gen = ng })
    | Just (smt_def, smt_def_e) <- E.lookupNameMod "spec" (Just "Spec") eenv
    , Just (try_unsafe, try_unsafe_e) <- E.lookupNameMod "tryMaybeUnsafe" (Just "Spec") eenv =
    let
        app_smt_def = mkApp $ Var (Id smt_def (typeOf tv_env smt_def_e)):map Var (inputIds s b)

        try_unsafe_var = Var . Id try_unsafe $ typeOf tv_env try_unsafe_e

        ret_type = returnType $ typeOf tv_env smt_def_e
        m_eq_dict = typeClassInst tc HM.empty (KV.eqTC kv) $ TyApp (tyMaybe kv) ret_type
    in
    case m_eq_dict of
        Just eq_dict ->
            let
                (val_name, ng') = freshSeededString "val" ng
                (comp_name, ng'') = freshSeededString "comp" ng'

                comp_e = mkApp [Var (Id (KV.eqFunc kv) TyUnknown)
                              , Type ret_type
                              , eq_dict
                              , App (App try_unsafe_var (Type ret_type)) app_smt_def
                              , App (App try_unsafe_var  (Type ret_type)) (Var $ Id val_name TyUnknown)]
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
synthFunc :: [ExecRes t] -> IO (Maybe SmtCmd)
synthFunc er = runSygus $ sygusCmds er

runSygus :: [Cmd] -> IO (Maybe SmtCmd)
runSygus sygus_cmds = do
    (h_in, h_out, _) <- getCVC5Sygus 60
    mapM_ (\c -> do
            T.hPutStrLn h_in $ printSygus c
            T.putStrLn $ printSygus c
        ) sygus_cmds
    _ <- hWaitForInput h_out 70
    out <- getLinesMatchParens h_out
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

sygusCmds :: [ExecRes t] -> [Cmd]
sygusCmds [] = []
sygusCmds er@(ExecRes { final_state = s@(State { tyvar_env = tv_env }), conc_args = args, conc_out = out_e}:_) = 
    let 
        define_eq n srt = SmtCmd $ DefineFun n
                                             [SortedVar "x" srt, SortedVar "y" srt]
                                             boolSort
                                             (TermCall (ISymb "=") [TermIdent (ISymb "x"), TermIdent (ISymb "y")])
        grm = GrammarDef pre_dec gram_defs'
    in
    [ SmtCmd $ SetLogic "ALL"
    , define_eq "strEq" strSort
    , define_eq "intEq" intSort
    , SynthFun "spec" arg_vars ret_sort (Just grm) ]
    ++ map execResToConstraints er ++
    [CheckSynth]
    where
        kv = known_values s

        intSort = IdentSort (ISymb "Int")
        strSort = IdentSort (ISymb "String")
        boolSort = IdentSort (ISymb "Bool")

        args_sort = map (typeToSort kv . typeOf tv_env) $ filter (not . isTYPE . typeOf tv_env) args
        arg_vars = map (uncurry SortedVar) $ zip argList args_sort
        ret_sort = typeToSort kv $ typeOf tv_env out_e

        intIdent = BfIdentifier (ISymb "IntPr")
        strIdent = BfIdentifier (ISymb "StrPr")
        boolIdent = BfIdentifier (ISymb "BoolPr")

        -------------------------------
        -- Grammar
        -------------------------------
        grmString = [ GVariable strSort
                    , GBfTerm (BfIdentifierBfs (ISymb "str.++") [ strIdent, strIdent])
                    , GBfTerm (BfIdentifierBfs (ISymb "str.substr") [ strIdent, intIdent, intIdent])
                    , GBfTerm (BfIdentifierBfs (ISymb "str.replace") [ strIdent, strIdent, strIdent])
                    , GBfTerm (BfIdentifierBfs (ISymb "str.replace_all") [ strIdent, strIdent, strIdent])
                    ]
        grmInt = [ GVariable intSort
                 , GBfTerm (BfLiteral (LitNum 0))
                 , GBfTerm (BfLiteral (LitNum (-1)))
                 , GBfTerm (BfIdentifierBfs (ISymb "str.indexof") [ strIdent, strIdent, intIdent ])
                 , GBfTerm (BfIdentifierBfs (ISymb "str.len") [ strIdent ])
                 , GBfTerm (BfIdentifierBfs (ISymb "+") [ intIdent, intIdent])
                 ]
        grmBool = [ GBfTerm (BfIdentifierBfs (ISymb "strEq") [ strIdent, strIdent ])
                  , GBfTerm (BfIdentifierBfs (ISymb "intEq") [ intIdent, intIdent ])
                  , GBfTerm (BfIdentifierBfs (ISymb "str.<") [ strIdent, strIdent ])
                  , GBfTerm (BfIdentifierBfs (ISymb "str.prefixof") [ strIdent, strIdent ])
                  , GBfTerm (BfIdentifierBfs (ISymb "str.suffixof") [ strIdent, strIdent ])
                  ]


        gram_defs = [ GroupedRuleList "StrPr" strSort grmString
                    , GroupedRuleList "IntPr" intSort grmInt
                    , GroupedRuleList "BoolPr" boolSort grmBool]
        find_start_gram = findElem (\(GroupedRuleList _ srt _) -> srt == ret_sort) gram_defs
        gram_defs' = case find_start_gram of
                            Just (start_sym, other_sym) -> start_sym:other_sym
                            Nothing -> error "runSygus: no start symbol"
        pre_dec = map (\(GroupedRuleList n srt _) -> SortedVar n srt) gram_defs'

findElem       :: (a -> Bool) -> [a] -> Maybe (a, [a])
findElem p     = find' id
    where
      find' _ []         = Nothing
      find' prefix (x : xs)
          | p x          = Just (x, prefix xs)
          | otherwise    = find' (prefix . (x:)) xs

varList :: String -> [String]
varList x = map ((++) x . show) [1 :: Integer ..]

argList :: [String]
argList = varList "z"

getCVC5Sygus :: Int -> IO (Handle, Handle, ProcessHandle)
getCVC5Sygus time_out = getProcessHandles $ proc "cvc5" ["--lang", "sygus", "--no-sygus-pbe", "--tlimit-per=" ++ show time_out]

parseSygus :: String -> [Cmd]
parseSygus = Sy.parse . Sy.lexSygus

execResToConstraints :: ExecRes t -> Cmd
execResToConstraints (ExecRes { final_state = s, conc_args = ars, conc_out = out_e }) =
    let
        kv = known_values s

        call = TermCall (ISymb "spec") (map (exprToTerm kv) $ relArgs ars)
        out_t = exprToTerm kv out_e
        cons = Constraint $ TermCall (ISymb "=") [call, out_t]
    in
    cons

relArgs :: [Expr] -> [Expr]
relArgs =  filter (not . isType)
    where 
        isType (Type _) = True
        isType _ = False

exprToTerm :: KnownValues -> Expr -> Term
exprToTerm _ (Lit (LitInt x)) = TermLit (LitNum x)
exprToTerm kv dc | dc == mkTrue kv = TermLit (LitBool True)
                 | dc == mkFalse kv = TermLit (LitBool False)
exprToTerm _ e | Just t <- toStringTerm e = t
exprToTerm _ e = error $ "exprToTerm: unsupported Expr" ++ "\n" ++ show e

toStringTerm :: Expr -> Maybe Term
toStringTerm e | Just s <- toString e =
    Just $ case go s of
                [x] -> x
                ys -> TermCall (ISymb "str.++") ys
    where
        go s = let (pre, post) = span isPrint s in
               case post of
                    "" -> [TermLit (LitStr pre)]
                    (non_pr:post') ->
                        let non_pr_t = TermCall (ISymb "str.from_code") [TermLit . LitNum . toInteger $ fromEnum non_pr] in
                        [TermLit (LitStr pre), non_pr_t] ++ go post'
toStringTerm _ = Nothing


typeToSort :: KnownValues -> Type -> Sort
typeToSort _ t | t == TyLitInt = IdentSort (ISymb "Int")
typeToSort kv t | t == tyBool kv = IdentSort (ISymb "Bool")
typeToSort kv (TyApp t _) | t == tyList kv = IdentSort (ISymb "String")
typeToSort _ s = error $ "typeToSort: unsupported Type" ++ "\n" ++ show s

-------------------------------------------------------------------------------
-- Turning a SyGuS solution into Haskell code
-------------------------------------------------------------------------------
termToHaskell :: Term -> String
termToHaskell trm =
    let
        (r, bind_p) = snd $ go 1 trm
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
        go !x (TermCall (ISymb "-") [TermLit (LitNum y)]) =(x, ("-" ++ show y ++ "#", []))
        go !x (TermCall (ISymb f) ts) =
            let
                (x', vl_args, arg_binds) = mapGo x ts
                vrs = intercalate " " vl_args
            in
            (x' + 1, ("y" ++ show x', arg_binds ++ ["!y" ++ show x' ++ " = " ++ smtFuncToPrim f ++ " " ++ vrs]))
        go !x (TermLet ls trm_l) =
            let
                (x', tss) = mapAccumL (\x_ (VarBinding n t) -> let (x_', (tc, ts)) = go x_ t in (x_', ts ++ ["!" ++ n ++ " = " ++ tc])) x ls
                (x'', (r, tss')) = go x' trm_l
            in
            (x'', (r, concat tss ++ tss'))
        go !x (TermLit l) = (x, (goLit l, []))
        go !_ t = error $ "termToHaskell: unsupported term" ++ "\n" ++ show t

        goLit (LitStr s) = "\"" ++ s ++ "\""
        goLit (LitNum i) = show i ++ "#"
        goLit _ = error "termToHaskell: unsupported lit"

smtFuncToPrim :: String -> String
smtFuncToPrim "str.++" = "strAppend#"
smtFuncToPrim "str.len" = "strLen#"
smtFuncToPrim "str.<" = "strLt#"
smtFuncToPrim "str.substr" = "strSubstr#"
smtFuncToPrim "str.prefixof" = "strPrefixOf#"
smtFuncToPrim "str.suffixof" = "strSuffixOf#"
smtFuncToPrim "str.indexof" = "strIndexOf#"
smtFuncToPrim "str.replace" = "strReplace#"
smtFuncToPrim "strEq" = "strEq#"
smtFuncToPrim "intEq" = "($==#)"
smtFuncToPrim "+" = "(+#)"
smtFuncToPrim f = error $ "smtFuncToPrim: unsupported " ++ f
