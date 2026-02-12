{-# LANGUAGE BangPatterns, FlexibleContexts, OverloadedStrings #-}

module G2.SMTSynth.Synthesizer ( SynthConfig (..)
                               , SynthMode (..)
                               
                               , getSeqGenConfig
                               , genSMTFunc
                               , adjustConfig
                               , seqGenConfig
                               , setSynthMode
                               , synthModeMapping
                               , runFunc
                               
                               , smtName
                               , smtNameWrap) where

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
import qualified Text.Builder as TB
import GHC.Plugins (IdDetails)

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

-- | Synthesizer specific configurations
data SynthConfig = SynthConfig { run_file :: String
                               , synth_func :: Maybe String -- ^ Synthesize a definition for a specific function
                               , eq_check :: String -- ^ Option to use as an equality check
                               , synth_mode :: SynthMode
                               , run_symex :: Bool -- ^ If true, run symbolic execution rather than synthesis
                               , g2_config :: Config
                               }

data SynthMode = SynthString | SynthSeqInt

synthModeMapping :: [(String, SynthMode)]
synthModeMapping = [("string", SynthString), ("seq-int", SynthSeqInt)]

getSeqGenConfig :: IO SynthConfig
getSeqGenConfig = do
    homedir <- getHomeDirectory
    sc <- execParser (seqGenConfig homedir)
    return $ sc { g2_config = adjustConfig (synth_mode sc) (g2_config sc)}

adjustConfig :: SynthMode -> Config -> Config
adjustConfig sm c =
    setSynthMode sm $ 
        c { step_limit = False
          , height_limit = Just $ fromMaybe 5 (height_limit c)

          , smt_prim_lists = UseSMTSeq { add_to_dcs = True, add_to_funcs = False }
          , search_strat = Subpath }

setSynthMode :: SynthMode -> Config -> Config
setSynthMode SynthString c = c { favor_tys = ["Char", "Integer"] }
setSynthMode SynthSeqInt c = c { favor_tys = ["Integer"] }

seqGenConfig :: String -> ParserInfo SynthConfig
seqGenConfig homedir =
    info ((SynthConfig
                <$> argument str (metavar "FILE")
                <*> option (eitherReader (Right . Just))
                   (long "function"
                   <> metavar "F"
                   <> value Nothing
                   <> help "a function to synthesize an SMT definition for")
                <*> option auto
                   (long "eq-check"
                   <> metavar "C"
                   <> value "=="
                   <> help "a function to use as an equality check")
                <*> option (maybeReader (flip lookup synthModeMapping))
                   (long "synth-mode"
                   <> metavar "M"
                   <> value SynthString
                   <> help ("synthesize functions for a specific type/using a specific SMT theory. Options: " ++ intercalate ", " (map fst synthModeMapping)))
                <*> flag False True (long "run-symex" <> help "Run symbolic execution on the passed function, rather than synthesis")
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
        varred_form' = addFromInteger varred_form
        lit_ers = execResCollectLits er
    in
    [PL { pattern = varred_form', lit_expr = conc_out er, pat_ids = is, orig_exec_res = [er], lit_vals = map (:[]) lit_ers }]
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
           -> Maybe (State t, Id, String) -- ^ Possible (SyGuS generated) function definition, along with the Id of the function being generated
           -> SynthConfig
           -> IO (String, String) -- ^ (Type of generated function, definition of generated function)
genSMTFunc pls src f smt_def sc@(SynthConfig { g2_config = config }) = do
    putStrLn "\n--- Running function --- "
    (entry_f, ers, ng) <- runFuncWithTemp src f smt_def sc
    case ers of
        [] | Just (s, (Id _ smt_t), smt_def') <- smt_def ->
                return (T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) smt_t), smt_def')
           | otherwise -> error "genSMTFunc: no SMT function generated" 
        (er@(ExecRes { final_state = s }):_) -> do
            putStrLn "\n--- Synthesizing --- "
            let pls' = foldr (insertER ng) pls ers

            new_smt_piece <- formFunction s pls'

            let kv = known_values s
                tv_env = tyvar_env s 
                
                vs = zipWith (formArg kv tv_env) argList (relArgs (final_state er) $ conc_args er)
                new_smt_def = T.unpack (smtNameWrap . smtName . nameOcc $ idName entry_f) ++ " " ++ intercalate " " vs ++ " = " ++ new_smt_piece
            genSMTFunc pls' src f (Just (final_state er, entry_f, new_smt_def)) sc

formArg :: KnownValues -> TyVarEnv -> String -> Expr -> String
formArg kv tv nm e
    | typeOf tv e == tyInt kv = "(I# " ++ nm ++ ")"
    | typeOf tv e == tyInteger kv = "(toInteger -> Z# " ++ nm ++ ")"
    | otherwise = nm

formFunction :: State t -> [PatternRes] -> IO String
formFunction _ [] = error "formFunction: empty list"
formFunction s [pr] = solveOnePattern s pr
formFunction s (pr:prs) = do
    putStrLn "\n* Solving Branch Condition"
    br <- solveBranchConditions s pr prs
    putStrLn "\n* Solving Pattern"
    r1 <- solveOnePattern s pr
    r2 <- formFunction s prs
    return $ "if " ++ br ++ " then " ++ r1 ++ " else " ++ r2

solveOnePattern :: State t -> PatternRes -> IO String
solveOnePattern s (PL { pattern = varred_form, pat_ids = is, lit_vals = constraints }) = do
    let is_constraints = zip is constraints

    let pg = mkPrettyGuide is
    new_pieces <- mapM (\(i@(Id _ t), constraints_) -> do
                            new_smt_def <- computeProdPieces constraints_
                            return $ "!" ++ T.unpack (printName pg (idName i)) ++ " = (" ++ new_smt_def ++ ")")
                        is_constraints
    let new_smt_def = "let " ++ intercalate "; " new_pieces ++ " in "
                    ++ T.unpack (toHaskellCode s pg varred_form)
    return new_smt_def

toHaskellCode :: State t -> PrettyGuide -> Expr -> T.Text
toHaskellCode _ _ e | Prim Error _:_ <- unApp e = "error \"\""
toHaskellCode s pg e = printHaskellPG pg s e

solveBranchConditions :: State t -> PatternRes -> [PatternRes] -> IO String
solveBranchConditions s@(State { known_values = kv }) pr prs = do
    let true_lv = map (setBool True) (orig_exec_res pr)
        false_lv = map (setBool False) (concatMap orig_exec_res prs)
        pat_id = Id (Name "g2__BOOL_ID" Nothing 0 Nothing) TyUnknown
        bool_pr = pr { pattern = Var pat_id, pat_ids = [pat_id], lit_vals = [true_lv ++ false_lv] }
    solveOnePattern s bool_pr
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

isList :: Expr -> Bool
isList (App (Data dc) (Type (TyCon n _)))
    | nameOcc (dcName dc) == "[]" = True
isList (App (App (App (Data dc) _) _) _)
    | nameOcc (dcName dc) == ":" = True
isList _ = False

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
            | nameOcc (dc_name dc) == "C#" = Var (Id (Name "!!__G2__!!_CHAR" Nothing 0 Nothing) TyUnknown)
            | otherwise = Data (dc { dc_name = Name (nameOcc (dc_name dc)) Nothing 0 Nothing})
        repLit e | isList e = Var (Id (Name "!!__G2__!!_LIST" Nothing 0 Nothing) TyUnknown)
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
modifyLits f e@(App (Data dc) _) | nameOcc (dc_name dc) == "C#" = f e
modifyLits f e | isList e = f e
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

addFromInteger :: Expr -> Expr
addFromInteger e@(App (Data dc) _) | nameOcc (dc_name dc) == "Z#" = App (Var $ Id (Name "fromInteger" Nothing 0 Nothing) TyUnknown) e
addFromInteger e = modifyChildren addFromInteger e

-------------------------------------------------------------------------------
-- Calling G2
-------------------------------------------------------------------------------

runFuncWithTemp :: [FilePath] -- ^ Filepath containing function
                -> T.Text -- ^ Function name
                -> Maybe (State t, Id, String) -- ^ Possible (SyGuS generated) function definition, along with the Id of the function being generated
                -> SynthConfig
                -> IO (Id, [ExecRes ()], NameGen)
runFuncWithTemp src f smt_def config = do
    withSystemTempFile "SpecTemp.hs" (\temp handle -> do
        setUpSpec config handle smt_def

        runFunc temp src f smt_def config
        )    

runFunc :: FilePath
        -> [FilePath] -- ^ Filepath containing function
        -> T.Text -- ^ Function name
        -> Maybe (State t, Id, String) -- ^ Possible (SyGuS generated) function definition, along with the Id of the function being generated
        -> SynthConfig
        -> IO (Id, [ExecRes ()], NameGen)
runFunc temp src f smt_def (SynthConfig { g2_config = config }) = do
    let config' = config { base = base config ++ temp:src, maxOutputs = Just 10}

    proj <- case src of
                src':_ -> guessProj (includePaths config') src'
                _ -> return []

    (init_state, entry_f, bindings, mb_modname) <- initialStateFromFile proj src
                                    Nothing False f (mkCurrExpr TV.empty Nothing Nothing) (mkArgTys config' TV.empty)
                                    simplTranslationConfig config'
    
    let comp_state = if isJust smt_def then findInconsistent entry_f init_state bindings else init_state
    -- let config'' = if isJust smt_def then config' { logStates = Log Pretty "a_smt"} else config'
    T.putStrLn $ printHaskellPG (mkPrettyGuide $ getExpr comp_state) comp_state (getExpr comp_state)

    (er, b, to) <- runG2WithConfig proj src entry_f f [] mb_modname comp_state config' bindings

    return (entry_f, er, name_gen bindings)

smtNameWrap :: T.Text -> T.Text
smtNameWrap n | Just (c, _) <- T.uncons n
              , isAlpha c = n
              | otherwise = "(" <> n <> ")"

smtName :: T.Text -> T.Text
smtName n | Just (c, _) <- T.uncons n
          , isAlpha c = "smt_" <> n
          | otherwise = "$!+$" <> n

setUpSpec :: SynthConfig -> Handle -> Maybe (State t, Id, String) -> IO ()
setUpSpec _ h Nothing = hClose h
setUpSpec sc h (Just (s@(State { known_values = kv }), Id n t, spec)) = do
    let ts = splitTyFuns
           . snd
           $ splitTyForAlls t
        t' = foldr1 TyFun
           . filter (not . isCallStack)
           $ ts
        vs = take (length ts - 1) argList
        vs_str = intercalate " " vs
        smt_name = T.unpack . smtNameWrap . smtName $ nameOcc n
        contents = "{-# LANGUAGE BangPatterns, MagicHash, ScopedTypeVariables, ViewPatterns #-}\nmodule Spec where\nimport GHC.Prim2\n"
                    ++ "import GHC.Types2\n"
                    ++ "import Control.Exception\n"
                    ++ "import System.IO.Unsafe\n\n"
                    ++ "tryMaybe :: IO a -> IO (Maybe a)\n"
                    ++ "tryMaybe a = catch (a >>= \\v -> return (Just v)) (\\(e :: SomeException) -> return Nothing)\n\n"
                    ++ "tryMaybeUnsafe :: a -> Maybe a\n"
                    ++ "tryMaybeUnsafe x = unsafePerformIO $ tryMaybe (let !y = x in return y)\n\n"
                    ++ smt_name ++ " :: " ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t') ++ "\n"
                    ++ spec
                    ++ "\n\ncomp :: ("
                            ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t')
                            ++ ") -> "
                            ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t') ++ "\n"
                    ++ "comp f " ++ vs_str ++ " = " ++ "\n    let val = f " ++ vs_str ++ ""  ++ " in\n"
                                                   ++ "    assert (tryMaybeUnsafe (" ++ smt_name ++ " " ++ vs_str ++ ") "
                                   ++ eq_check sc ++ " tryMaybeUnsafe val) val"
    putStrLn contents
    hPutStrLn h contents
    hFlush h
    hClose h

isCallStack :: Type -> Bool
isCallStack ty | TyCon tn _:_ <- unTyApp ty = nameOcc tn == "IP"
               | otherwise = False

-- | Find inputs that violate a found SMT definition
findInconsistent :: Id -> State t -> Bindings -> State t
findInconsistent entry_f s@(State { expr_env = eenv
                                  , tyvar_env = tv_env }) b
    | Just (comp_name, _) <- E.lookupNameMod "comp" (Just "Spec") eenv =
        let
            new_curr_expr = mkApp $ Var (Id comp_name TyUnknown):Var entry_f:fixed_inputs b
                            ++ filter (not . isCallStack . typeOf tv_env) (map Var (inputIds s b))
        in
        s { curr_expr = CurrExpr Evaluate new_curr_expr
          , true_assert = False }
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
    _ <- hWaitForInput h_out 1000
    out <- getLinesMatchParens h_out
    _ <- evaluate (length out)
    putStrLn out
    T.hPutStrLn h_in "(exit)"
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
sygusCmds er@(ExecRes { final_state = s@(State { tyvar_env = tv_env, known_values = kv }), conc_args = args, conc_out = out_e}:_) = 
    let 
        define_eq n srt = SmtCmd $ DefineFun n
                                             [SortedVar "x" srt, SortedVar "y" srt]
                                             boolSort
                                             (TermCall (ISymb "=") [TermIdent (ISymb "x"), TermIdent (ISymb "y")])
        from_char = SmtCmd $ DefineFun "fromChar"
                                        [SortedVar "x" strSort]
                                        strSort
                                        (TermIdent (ISymb "x"))
        -- toChar returns the first character of a non-empty string, or "" if passed an empty string.
        -- This is not possible to reflect in the actual Haskell code, where a Char must be exactly one character.
        -- Thus, we carefully arrange the grammar so that `toChar` can only appear as the outermost function.
        -- If it returns an empty string, this will be different than the Haskell code, which must have some other behavior-
        -- and so our CEGIS synthesizer will have an error to loop on.
        to_char = SmtCmd $ DefineFun "toChar"
                                        [SortedVar "x" strSort]
                                        strSort
                                        ( TermCall (ISymb "str.at") [TermIdent (ISymb "x"), TermLit (LitNum 0)] )
        grm = GrammarDef pre_dec gram_defs'
    in
    [ SmtCmd $ SetLogic "ALL"
    , define_eq "strEq" strSort
    , define_eq "seqIntEq" seq_int_sort
    , define_eq "intEq" intSort
    , from_char
    , to_char
    , SynthFun "spec" arg_vars ret_sort (Just grm) ]
    ++ map execResToConstraints er ++
    [CheckSynth]
    where
        intSort = IdentSort (ISymb "Int")
        floatSort = IdentSort (ISymb "Float32")
        strSort = IdentSort (ISymb "String")
        boolSort = IdentSort (ISymb "Bool")

        arg_types = map (typeOf tv_env) $ relArgs s args
        args_sort = map (typeToSort kv) arg_types
        arg_vars = zipWith SortedVar argList args_sort

        ret_type = typeOf tv_env out_e
        ret_sort = typeToSort kv ret_type

        char_args = map fst . filter ((==) (tyChar kv) . snd) $ zip argList arg_types
        str_args = map fst . filter ((==) (tyString kv) . snd) $ zip argList arg_types

        intIdent = BfIdentifier (ISymb "IntPr")
        floatIdent = BfIdentifier (ISymb "FloatPr")
        charArgIdent = BfIdentifier (ISymb "CharArgPr")
        strIdent = BfIdentifier (ISymb "StrPr")
        seqIntIdent = BfIdentifier (ISymb "SeqIntPr")
        seqFloatIdent = BfIdentifier (ISymb "SeqFloatPr")
        boolIdent = BfIdentifier (ISymb "BoolPr")

        -------------------------------
        -- Grammar
        -------------------------------
        grmString = map (GBfTerm . BfIdentifier . ISymb) str_args
                    ++
                    [ GBfTerm (BfIdentifierBfs (ISymb "ite") [ boolIdent, strIdent, strIdent])
                    , GBfTerm (BfLiteral (LitStr ""))
                    , GBfTerm (BfIdentifierBfs (ISymb "seq.++") [ strIdent, strIdent])
                    , GBfTerm (BfIdentifierBfs (ISymb "seq.at") [ strIdent, intIdent])
                    , GBfTerm (BfIdentifierBfs (ISymb "seq.extract") [ strIdent, intIdent, intIdent])
                    , GBfTerm (BfIdentifierBfs (ISymb "seq.replace") [ strIdent, strIdent, strIdent])
                    -- , GBfTerm (BfIdentifierBfs (ISymb "str.replace_all") [ strIdent, strIdent, strIdent])
                    ]
                    ++
                    if not (null char_args) then [GBfTerm (BfIdentifierBfs (ISymb "fromChar") [ charArgIdent ])] else []
        grmCharArgs = map (GBfTerm . BfIdentifier . ISymb) char_args
        grmCharRet = [ GBfTerm (BfIdentifierBfs (ISymb "toChar") [ strIdent ])]
        grmInt = [ GVariable intSort
                 , GBfTerm (BfIdentifierBfs (ISymb "ite") [ boolIdent, intIdent, intIdent])
                 , GBfTerm (BfLiteral (LitNum 0))
                 , GBfTerm (BfLiteral (LitNum (-1)))
                 , GBfTerm (BfIdentifierBfs (ISymb "+") [ intIdent, intIdent])
                 ]
                 ++ intOpForIdent strIdent
                 ++ intOpForIdent seqIntIdent
        intOpForIdent ident =
                 [
                   GBfTerm (BfIdentifierBfs (ISymb "seq.indexof") [ ident, ident, intIdent ])
                 , GBfTerm (BfIdentifierBfs (ISymb "seq.len") [ ident ])
                 ]
        grmFloat = [ GVariable floatSort
                   , GBfTerm (BfIdentifierBfs (ISymb "ite") [ boolIdent, floatIdent, floatIdent])
                   , GBfTerm (BfLiteral (LitNum 0))
                   , GBfTerm (BfLiteral (LitNum (-1)))
                   , GBfTerm (BfIdentifierBfs (ISymb "+") [ floatIdent, floatIdent])
                   ]

        grmBool = [ GBfTerm (BfIdentifierBfs (ISymb "ite") [ boolIdent, boolIdent, boolIdent])
                  , GBfTerm (BfIdentifierBfs (ISymb "intEq") [ intIdent, intIdent ])
                  , GBfTerm (BfIdentifierBfs (ISymb "str.<") [ strIdent, strIdent ])
                  , GBfTerm (BfIdentifierBfs (ISymb "str.<=") [ strIdent, strIdent ])
                  ]
                  ++ boolOpForIdent "strEq" strIdent
                  ++ boolOpForIdent "seqIntEq" seqIntIdent
        boolOpForIdent comp ident = 
                  [ GBfTerm (BfIdentifierBfs (ISymb comp) [ ident, ident ])
                  , GBfTerm (BfIdentifierBfs (ISymb "seq.prefixof") [ ident, ident ])
                  , GBfTerm (BfIdentifierBfs (ISymb "seq.suffixof") [ ident, ident ])
                  , GBfTerm (BfIdentifierBfs (ISymb "seq.contains") [ ident, ident ])
                  ]

        grmSeq srt srtIdent =
                     [ GVariable srt
                     , GBfTerm (BfIdentifierBfs (ISymb "ite") [ boolIdent, srtIdent, srtIdent])
                     , GBfTerm (BfIdentifierBfs (ISymb "as") [BfIdentifier (ISymb "seq.empty"), BfIdentifier (ISymb . T.unpack $ printSygus srt) ])
                     , GBfTerm (BfIdentifierBfs (ISymb "seq.++") [ srtIdent, srtIdent])
                     , GBfTerm (BfIdentifierBfs (ISymb "seq.at") [ srtIdent, intIdent])
                     , GBfTerm (BfIdentifierBfs (ISymb "seq.extract") [ srtIdent, intIdent, intIdent])
                     , GBfTerm (BfIdentifierBfs (ISymb "seq.replace") [ srtIdent, srtIdent, srtIdent])
                     -- , GBfTerm (BfIdentifierBfs (ISymb "str.replace_all") [ strIdent, strIdent, strIdent])
                     ]

        seq_int_sort = IdentSortSort (ISymb "Seq") [IdentSort (ISymb "Int")]
        seq_float_sort = IdentSortSort (ISymb "Seq") [IdentSort (ISymb "Float32")]

        ty_gram_defs = (if ret_type == tyChar kv then ((tyChar kv, GroupedRuleList "CharRetPr" strSort grmCharRet):) else id) $
                       (if not (null char_args) then ((tyChar kv, GroupedRuleList "CharArgPr" strSort grmCharArgs):) else id)           
                       [ (tyString kv, GroupedRuleList "StrPr" strSort grmString)
                       , (TyApp (tyList kv) (tyInt kv), GroupedRuleList "SeqIntPr" seq_int_sort (grmSeq seq_int_sort seqIntIdent))
                       , (TyApp (tyList kv) (tyFloat kv), GroupedRuleList "SeqFloatPr" seq_float_sort (grmSeq seq_float_sort seqFloatIdent))
                       , (TyLitInt, GroupedRuleList "IntPr" intSort grmInt)
                       , (tyBool kv, GroupedRuleList "BoolPr" boolSort grmBool)]
        find_start_gram = findElem (\(ty, _) -> ty == ret_type) ty_gram_defs
        gram_defs' = case find_start_gram of
                            Just (start_sym, other_sym) -> map snd $ start_sym:other_sym
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
getCVC5Sygus time_out = getProcessHandles $ proc "cvc5" ["--lang", "sygus", "--tlimit-per=" ++ show time_out]

parseSygus :: String -> [Cmd]
parseSygus = Sy.parse . Sy.lexSygus

execResToConstraints :: ExecRes t -> Cmd
execResToConstraints (ExecRes { final_state = s, conc_args = ars, conc_out = out_e }) =
    let
        kv = known_values s

        call = TermCall (ISymb "spec") (map (exprToTerm kv) $ relArgs s ars)
        out_t = exprToTerm kv out_e
        cons = Constraint $ TermCall (ISymb "=") [call, out_t]
    in
    cons

relArgs :: State t -> [Expr] -> [Expr]
relArgs s = filter (not . isCallStack . typeOf (tyvar_env s))
          . filter (not . isTypeClass (type_classes s) . typeOf (tyvar_env s))
          . filter (not . isType)
    where 
        isType (Type _) = True
        isType _ = False

exprToTerm :: KnownValues -> Expr -> Term
exprToTerm _ (Lit (LitInt x)) = TermLit (LitNum x)
exprToTerm _ (Lit (LitChar x)) = toStringTerm [x]
exprToTerm _ (App _ (Lit (LitInt x))) = TermLit (LitNum x)
exprToTerm _ (App _ (Lit (LitFloat x))) = TermIdent . ISymb . T.unpack . TB.run $ convertFloating castFloatToWord32 8 x
exprToTerm _ (App _ (Lit (LitChar x))) = toStringTerm [x]
exprToTerm kv dc | dc == mkTrue kv = TermLit (LitBool True)
                 | dc == mkFalse kv = TermLit (LitBool False)
exprToTerm _ e | Just t <- toStringTermFromExpr e = t
exprToTerm kv e | Just t <- toSeqTermFromExpr kv e = t
exprToTerm _ e = error $ "exprToTerm: unsupported Expr" ++ "\n" ++ show e

toStringTermFromExpr :: Expr -> Maybe Term
toStringTermFromExpr e | Just s <- toString e = Just $ toStringTerm s
                       | otherwise = Nothing

toStringTerm :: String -> Term
toStringTerm s =
    case go s of
            [x] -> x
            ys -> TermCall (ISymb "seq.++") ys
    where
        go s = let (pre, post) = span isPrint s in
               case post of
                    "" -> [TermLit (LitStr pre)]
                    (non_pr:post') ->
                        let non_pr_t = TermCall (ISymb "str.from_code") [TermLit . LitNum . toInteger $ fromEnum non_pr] in
                        [TermLit (LitStr pre), non_pr_t] ++ go post'

toSeqTermFromExpr :: KnownValues -> Expr -> Maybe Term
toSeqTermFromExpr kv e | Just s <- toExprList e = Just $ toSeqTerm kv (exprListType e) s
                       | otherwise = Nothing

exprListType :: Expr -> Type
exprListType e | _:Type t:_ <- unApp e = t
exprListType e = error $ "exprListType: Not a list" ++ show e

toSeqTerm :: KnownValues -> Type -> [Expr] -> Term
toSeqTerm kv t [] =
    let
        sortToTerm (IdentSort (ISymb "String")) = TermIdent (ISymb "String")
        sortToTerm (IdentSort s) = TermCall (ISymb "Seq") [ TermIdent s]
        sortToTerm (IdentSortSort s xs) = TermCall s $ map sortToTerm xs
    in
    TermCall (ISymb "as") [ TermIdent (ISymb "seq.empty"), sortToTerm $ typeToSort kv t ]
toSeqTerm kv t (x:xs) = TermCall (ISymb "seq.++") [ TermCall (ISymb "seq.unit") [ exprToTerm kv x ]
                                                  , toSeqTerm kv t xs]

typeToSort :: KnownValues -> Type -> Sort
typeToSort _ t | t == TyLitInt = IdentSort (ISymb "Int")
typeToSort _ t | t == TyLitChar = IdentSort (ISymb "String")
typeToSort kv t | t == tyBool kv = IdentSort (ISymb "Bool")
typeToSort kv (TyApp t1 t2) | t1 == tyList kv
                            , t2 == tyChar kv = IdentSort (ISymb "String")
typeToSort kv (TyApp t1 t2) | t1 == tyList kv = IdentSortSort (ISymb "Seq") [ typeToSort kv t2 ]
typeToSort kv t | t == tyInt kv = IdentSort (ISymb "Int")
typeToSort kv t | t == tyInteger kv = IdentSort (ISymb "Int")
typeToSort kv t | t == tyFloat kv = IdentSort (ISymb "Float32")
typeToSort kv t | t == tyChar kv = IdentSort (ISymb "String")
typeToSort _ TyUnknown = IdentSort (ISymb ("Unknown"))
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
        go !x (TermCall (ISymb "as") (TermIdent (ISymb "seq.empty"):_)) = (x, ("[]", []))
        go !x (TermCall (ISymb f) ts) =
            let
                (x', vl_args, arg_binds) = mapGo x ts
            in
            (x' + 1, ("y" ++ show x', arg_binds ++ ["!y" ++ show x' ++ " = " ++ smtFuncToPrim f vl_args]))
        go !x (TermLet ls trm_l) =
            let
                (x', tss) = mapAccumL (\x_ (VarBinding n t) -> let (x_', (tc, ts)) = go x_ t in (x_', ts ++ ["!" ++ n ++ " = " ++ tc])) x ls
                (x'', (r, tss')) = go x' trm_l
            in
            (x'', (r, concat tss ++ tss'))
        go !x (TermLit l) = (x, (goLit l, []))
        go !_ t = error $ "termToHaskell: unsupported term" ++ "\n" ++ show t

        goLit (LitStr []) = "[]"
        goLit (LitStr s) = "\"" ++ s ++ "\""
        goLit (LitNum i) = show i ++ "#"
        goLit _ = error "termToHaskell: unsupported lit"

smtFuncToPrim :: String -> [String] -> String
smtFuncToPrim s vl_args = conv s ++ conv_args
    where
        conv "str.++" = "strAppend# "
        conv "str.len" = "strLen#"
        conv "str.<" = "strLt#"
        conv "str.<=" = "strLe#"
        conv "str.at" = "strAt#"
        conv "str.substr" = "strSubstr#"
        conv "str.prefixof" = "strPrefixOf#"
        conv "str.suffixof" = "strSuffixOf#"
        conv "str.contains" = "strContains#"
        conv "str.indexof" = "strIndexOf#"
        conv "str.replace" = "strReplace#"
        conv "strEq" = "strEq#"

        conv "seq.++" = "strAppend# "
        conv "seq.len" = "strLen#"
        conv "seq.at" = "strAt#"
        conv "seq.extract" = "strSubstr#"
        conv "seq.prefixof" = "strPrefixOf#"
        conv "seq.suffixof" = "strSuffixOf#"
        conv "seq.contains" = "strContains#"
        conv "seq.indexof" = "strIndexOf#"
        conv "seq.replace" = "strReplace#"
        conv "seqIntEq" = "strEq#"

        conv "intEq" = "($==#)"
        conv "fromChar" = ""
        conv "toChar" = ""
        conv "+" = "(+#)"
        conv "ite" = ""

        conv f = error $ "smtFuncToPrim: unsupported " ++ f
        
        conv_args = case s of
                        "ite" | [a1, a2, a3] <- vl_args -> "(if " ++ a1 ++ " then " ++ a2 ++ " else " ++ a3 ++ ")"
                              | otherwise -> error "smtFuncToPrim: ite wrong arg count"
                        -- We wrap list values in id to ensure that strict let expressions do not get shifted into variable args.
                        -- GHC may rewrite:
                        --     @ let !x = ['a'] in strAppend# x y @
                        -- to 
                        --     @ strAppend# (let !x = ['a'] in x) y @
                        -- because ['a'] is already in WHNF.  But this then breaks G2, because strAppend# cannot handle its
                        -- first argument being a let expression.
                        "fromChar" | [a] <- vl_args -> "id [" ++ a ++ "]"
                                   | otherwise -> error "smtFuncToPrim: fromChar wrong arg count"
                        "toChar" | [a] <- vl_args ->
                                            let
                                                b1 = "!len__G2__INT = strLen# " ++ a
                                                b2 = "!at_G2_STR = (strAt# " ++ a ++ " 0#)"
                                                let_b = "let " ++ b1 ++ ";" ++ b2 ++ "in"
                                            in
                                            "(case (" ++ let_b ++ " at_G2_STR) of [x] -> x)"
                        _ -> " " ++ intercalate " " vl_args

