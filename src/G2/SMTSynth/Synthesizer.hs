{-# LANGUAGE BangPatterns, FlexibleContexts, OverloadedStrings #-}

module G2.SMTSynth.Synthesizer ( SynthConfig (..)
                               , SynthMode (..)
                               , Checking (..)
                               
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
import G2.Initialization.KnownValues
import G2.Initialization.MkCurrExpr
import G2.Interface
import G2.Language as G2 hiding (Handle)
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.KnownValues as KV
import G2.Language.Monad
import qualified G2.Language.Typing as Ty
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
import System.FilePath
import System.IO
import System.IO.Temp
import System.Process
import qualified Text.Builder as TB
import Debug.Trace

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
                               , checking :: Checking
                               , synth_func :: Maybe String -- ^ Synthesize a definition for a specific function
                               , eq_check :: String -- ^ Function to use as an equality check
                               , eq_file :: Maybe FilePath -- ^ File containing function to use as an equality check
                               , synth_mode :: SynthMode
                               , run_symex :: Bool -- ^ If true, run symbolic execution rather than synthesis
                               , specs_type :: SpecType -- ^ Synthesize function specification or SMT function
                               , timeout :: Int -- ^ Sets the timeout (in seconds) for the Sygus solver
                               , g2_config :: Config
                               }

data Checking = Verify | ADTHeight deriving Eq
data SynthMode = SynthString | SynthSeqInt deriving Eq
data SpecType = FuncSpecs | SMTFunc deriving Eq

synthModeMapping :: [(String, SynthMode)]
synthModeMapping = [("String", SynthString), ("SeqInt", SynthSeqInt)]

getSeqGenConfig :: IO SynthConfig
getSeqGenConfig = do
    homedir <- getHomeDirectory
    sc <- execParser (seqGenConfig homedir)
    return $ sc { g2_config = adjustConfig sc (g2_config sc)}

adjustConfig :: SynthConfig -> Config -> Config
adjustConfig sc c =
    setSynthMode (synth_mode sc) $ 
        c { step_limit = False
          , height_limit = if checking sc == ADTHeight then Just $ fromMaybe 5 (height_limit c) else Nothing

          , smt_prim_lists = UseSMTSeq { add_to_dcs = True, add_to_funcs = False }
          , search_strat = Subpath }

setSynthMode :: SynthMode -> Config -> Config
setSynthMode SynthString c = c { favor_tys = ["Char", "Integer"] }
setSynthMode SynthSeqInt c = c { favor_tys = ["Integer"] }

seqGenConfig :: String -> ParserInfo SynthConfig
seqGenConfig homedir =
    info ((SynthConfig
                <$> argument str (metavar "FILE")
                <*> flag ADTHeight Verify
                   (long "verify"
                   <> help "a function to synthesize an SMT definition for")
                <*> option (eitherReader (Right . Just))
                   (long "function"
                   <> metavar "F"
                   <> value Nothing
                   <> help "a function to synthesize an SMT definition for")
                <*> option (eitherReader (Right))
                   (long "eq-check"
                   <> metavar "C"
                   <> value "=="
                   <> help "a function to use as an equality check")
                <*> option (maybeReader (Just . Just))
                   (long "eq-file"
                   <> metavar "F"
                   <> value Nothing
                   <> help "a file containing an equality check")
                <*> option (maybeReader (flip lookup synthModeMapping))
                   (long "synth-mode"
                   <> metavar "M"
                   <> value SynthString
                   <> help ("synthesize functions for a specific type/using a specific SMT theory. Options: " ++ intercalate ", " (map fst synthModeMapping)))
                <*> flag False True (long "run-symex" <> help "Run symbolic execution on the passed function, rather than synthesis")
                <*> flag SMTFunc FuncSpecs (long "func-specs" <> help "Generates specifications for functions")
                <*> option auto (long "timeout"
                   <> metavar "T"
                   <> value 1000
                   <> help "sets the timeout (in seconds) for the sygus solver")
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
           -> Maybe (State t, Id, String, String) -- ^ Possible (SyGuS generated) function definition, along with the Id of the function being generated
           -> SynthConfig
           -> IO (String, String) -- ^ (Type of generated function, definition of generated function)
genSMTFunc pls src f smt_def sc@(SynthConfig { g2_config = config }) = do
    putStrLn "\n--- Running function --- "
    (entry_f, ers, ng, isSpecCorrect) <- runFuncWithTemp src f smt_def sc
    case ers of
        [] | Just (s, (Id _ smt_t), smt_def', _) <- smt_def ->
                return (T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) smt_t), smt_def')
           | otherwise -> error "genSMTFunc: no SMT function generated" 
        (er@(ExecRes { final_state = s }):_) -> do
            putStrLn "\n--- Synthesizing --- "
            let pls' = foldr (insertER ng) pls ers
                smt_spec' = case smt_def of
                            Just (_,_,_,smt_spec) -> Just smt_spec
                            Nothing -> Nothing


            (new_smt_piece, smt_spec'') <- formFunction s pls' sc smt_spec' isSpecCorrect

            let kv = known_values s
                tv_env = tyvar_env s 

                vs = zipWith (formArg kv tv_env) argList (relArgs (final_state er) $ conc_args er)
                new_smt_def = T.unpack (smtNameWrap . smtName . nameOcc $ idName entry_f) ++ " " ++ intercalate " " vs ++ " = " ++ new_smt_piece
            genSMTFunc pls' src f (Just (final_state er, entry_f, new_smt_def, smt_spec'')) sc

formArg :: KnownValues -> TyVarEnv -> String -> Expr -> String
formArg kv tv nm e
    | typeOf tv e == tyInt kv = "(I# " ++ nm ++ ")"
    | typeOf tv e == tyInteger kv = "(toInteger -> Z# " ++ nm ++ ")"
    | otherwise = nm


-- Question: Ask Bill
formFunction :: State t -> [PatternRes] -> SynthConfig -> Maybe String -> Maybe Bool -> IO (String, String)
formFunction _ [] _ _ _ = error "formFunction: empty list"
formFunction s [pr] sc smt_def is_spec_correct = solveOnePattern s pr sc smt_def is_spec_correct
formFunction s (pr:prs) sc smt_def is_spec_correct = do
    putStrLn "\n* Solving Branch Condition"
    (br, _) <- solveBranchConditions s pr prs sc smt_def is_spec_correct
    putStrLn "\n* Solving Pattern"
    (r1, smt_spec) <- solveOnePattern s pr sc smt_def is_spec_correct
    (r2, _) <- formFunction s prs sc smt_def is_spec_correct
    return  ("if " ++ br ++ " then " ++ r1 ++ " else " ++ r2, smt_spec)

solveOnePattern :: State t -> PatternRes -> SynthConfig -> Maybe String -> Maybe Bool -> IO (String, String)
solveOnePattern s (PL { pattern = varred_form, pat_ids = is, lit_vals = constraints }) sc smt_def is_spec_correct = do
    let is_constraints = zip is constraints

    let pg = mkPrettyGuide is
    new_pieces <- mapM (\(i@(Id _ t), constraints_) -> do
                            (new_smt_def, smt_spec) <- computeProdPieces constraints_ sc smt_def is_spec_correct
                            let res = "!" ++ T.unpack (printName pg (idName i)) ++ " = (" ++ new_smt_def ++ ")"
                            return  (res, smt_spec))
                        is_constraints
    let new_pieces' = map fst new_pieces
        smt_spec = map snd new_pieces                  
        new_smt_def = "let " ++ intercalate "; " new_pieces' ++ " in "
                    ++ T.unpack (toHaskellCode s pg varred_form)
    return (new_smt_def, head smt_spec)

toHaskellCode :: State t -> PrettyGuide -> Expr -> T.Text
toHaskellCode _ _ e | Prim Error _:_ <- unApp e = "error \"\""
toHaskellCode s pg e = printHaskellPG pg s e

solveBranchConditions :: State t -> PatternRes -> [PatternRes] -> SynthConfig -> Maybe String -> Maybe Bool -> IO (String, String)
solveBranchConditions s@(State { known_values = kv }) pr prs sc smt_def is_spec_correct = do
    let true_lv = map (setBool True) (orig_exec_res pr)
        false_lv = map (setBool False) (concatMap orig_exec_res prs)
        pat_id = Id (Name "g2__BOOL_ID" Nothing 0 Nothing) TyUnknown
        bool_pr = pr { pattern = Var pat_id, pat_ids = [pat_id], lit_vals = [true_lv ++ false_lv] }
    solveOnePattern s bool_pr sc smt_def is_spec_correct
    where
        setBool b er = er { final_state = (final_state er) {curr_expr = CurrExpr Return (mkBool kv b)}, conc_out = mkBool kv b }


computeProdPieces :: [ExecRes t] -> SynthConfig -> Maybe String -> Maybe Bool -> IO (String, String)
computeProdPieces constraints sc smt_def is_spec_correct= do
    smt_strs <- synthFunc constraints sc smt_def is_spec_correct
    case smt_strs of
        Just (smt_cmd@(DefineFun _ _ _ t), smt_spec) -> do 
            print smt_cmd
            return (termToHaskell t, smt_spec)
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
                -> Maybe (State t, Id, String, String) -- ^ Possible (SyGuS generated) function definition, along with the Id of the function being generated
                -> SynthConfig
                -> IO (Id, [ExecRes ()], NameGen, Maybe Bool)
runFuncWithTemp src f smt_def config = do
    withSystemTempFile "SpecTemp.hs" (\temp handle -> do
        setupSpecFuncOrSMT src f config handle smt_def

        runFunc temp src f smt_def config
        )

runFunc :: FilePath
        -> [FilePath] -- ^ Filepath containing function
        -> T.Text -- ^ Function name
        -> Maybe (State t, Id, String, String) -- ^ Possible (SyGuS generated) function definition, along with the Id of the function being generated
        -> SynthConfig
        -> IO (Id, [ExecRes ()], NameGen, Maybe Bool)
runFunc temp src f smt_def sc = do
    case specs_type sc of
        SMTFunc -> runFuncSMT temp src f smt_def sc
        FuncSpecs -> runFuncSpec temp src f smt_def sc


runFuncSMT :: FilePath
        -> [FilePath] -- ^ Filepath containing function
        -> T.Text -- ^ Function name
        -> Maybe (State t, Id, String, String) -- ^ Possible (SyGuS generated) function definition, along with the Id of the function being generated
        -> SynthConfig
        -> IO (Id, [ExecRes ()], NameGen, Maybe Bool)
runFuncSMT temp src f smt_def sc@(SynthConfig { eq_file = eq_f, g2_config = config }) = do
    let extra_fp = maybeToList eq_f
        config' = config { base = base config ++ extra_fp ++ temp:src
                         , baseInclude = map takeDirectory extra_fp ++ baseInclude config
                         , maxOutputs = Just 10}

    proj <- case src of
                src':_ -> guessProj (includePaths config') src'
                _ -> return []

    let f' = if isJust smt_def then "comp" else f
    (init_state, func, bindings, mb_modname) <- initialStateFromFile proj src
                                    Nothing False f' (mkCurrExpr TV.empty Nothing Nothing) (mkArgTys config' TV.empty)
                                    simplTranslationConfig config'

    let (comp_state, entry_f) = case smt_def of
                        Just (_, i@(Id n _), _, _) | Just (entry_f_n, entry_f_def) <- E.lookupNameMod (nameOcc n) (nameModule n) (expr_env init_state) ->
                                            let
                                                new_i = Id entry_f_n $ typeOf (tyvar_env init_state) entry_f_def
                                            in
                                            (findInconsistent new_i init_state bindings False, new_i)
                                       | otherwise -> error "runFunc: func not found" 
                        Nothing -> (init_state, func)
    -- let config'' = if isJust smt_def then config' { logStates = Log Pretty "a_smt"} else config'
    T.putStrLn $ printHaskellPG (mkPrettyGuide $ getExpr comp_state) comp_state (getExpr comp_state)

    let comp_state' = if checking sc == Verify then setUpVerification (idName entry_f) comp_state else comp_state

    (er, b, to) <- runG2WithConfig proj src entry_f f [] mb_modname comp_state' config' bindings

    return (entry_f, er, name_gen bindings, Nothing)

runFuncSpec :: FilePath
        -> [FilePath] -- ^ Filepath containing function
        -> T.Text -- ^ Function name
        -> Maybe (State t, Id, String, String)
        -> SynthConfig
        -> IO (Id, [ExecRes ()], NameGen, Maybe Bool)
runFuncSpec temp src f smt_def sc@(SynthConfig { eq_file = eq_f, g2_config = config }) = do
    let extra_fp = maybeToList eq_f
        config' = config { base = base config ++ extra_fp ++ temp:src
                         , baseInclude = map takeDirectory extra_fp ++ baseInclude config
                         , maxOutputs = Just 10}

    proj <- case src of
                src':_ -> guessProj (includePaths config') src'
                _ -> return []
    -- This extra step is to retrieve original function Id
    (_, func@(Id n _), _, _) <- initialStateFromFile proj src
                                    Nothing False f (mkCurrExpr TV.empty Nothing Nothing) (mkArgTys config' TV.empty)
                                    simplTranslationConfig config'
    (comp_state, comp_func, comp_bindings, comp_mb_modname) <- initialStateFromFile proj src
                                    Nothing False "comp" (mkCurrExpr TV.empty Nothing Nothing) (mkArgTys config' TV.empty)
                                    simplTranslationConfig config'
    
    let (comp_state', entry_f) = case E.lookupNameMod (nameOcc n) (nameModule n) (expr_env comp_state) of
            Just (entry_f_n, entry_f_def) | isJust smt_def -> 
                let new_i = Id entry_f_n $ typeOf (tyvar_env comp_state) entry_f_def
                    in (findInconsistent new_i comp_state comp_bindings False, new_i)
            Just (entry_f_n, entry_f_def) -> 
                let new_i = Id entry_f_n $ typeOf (tyvar_env comp_state) entry_f_def
                    in (findInconsistent new_i comp_state comp_bindings True, new_i)
            Nothing -> (comp_state, func)

    -- let config'' = if isJust smt_def then config' { logStates = Log Pretty "a_smt"} else config'
    let config'' = config'
    T.putStrLn $ printHaskellPG (mkPrettyGuide $ getExpr comp_state') comp_state' (getExpr comp_state')

    let (comp_state'', ng) = if checking sc == Verify then verifySpec (idName entry_f) (idName comp_func) comp_bindings comp_state' else (comp_state', name_gen comp_bindings)

    (er, _, _) <- runG2WithConfig proj src comp_func "comp" [] comp_mb_modname comp_state'' config'' comp_bindings

    let isSpecCorrect = case smt_def of
                            Just _ -> checkIfSpecIsCorrect er
                            _ -> Nothing
    
    return (comp_func, er, ng, isSpecCorrect)

    where
        checkIfSpecIsCorrect [] = Just True 
        checkIfSpecIsCorrect (er@(ExecRes { final_state = s, conc_out = out_e }):es) =
            if out_e == mkTrue (known_values s)
                then Just False
                else checkIfSpecIsCorrect es

        verifySpec :: Name -> Name -> Bindings -> State t -> (State t, NameGen)
        verifySpec entry_n comp_f_n b@Bindings {name_gen = ng} s@(State { expr_env = eenv, known_values = kv, tyvar_env = tvnv })
            | Just entry_e <- E.lookup entry_n eenv
            , Just (_, smt_e) <- E.lookupNameMod (smtName $ nameOcc comp_f_n) (Just "Spec") eenv
            , Just (placeholder_n, place_e) <- E.lookupNameMod "placeholder" (Just "Spec") eenv
            , Just (placeholder_ret_n, _) <- E.lookupNameMod "placeholderRet" (Just "Spec") eenv
            , Just (ideal_n, ideal_e) <- E.lookupNameMod (T.pack ("ideal_" ++ (T.unpack $ nameOcc comp_f_n))) (Just "Spec") eenv
            , Just (ideal_ret_n, _) <- E.lookupNameMod "idealRet" (Just "Spec") eenv =
                let t = Ty.typeOf tvnv entry_e
                    tys = splitTyFuns t
                    (xIds, ng') = freshIds tys ng
                    inputExprs = map Var xIds
                    spec_call_expr = mkApp $ smt_e : inputExprs
                    replace_rec_fun = Let [(last xIds, SymGen SNoLog (last tys))] (Assume Nothing spec_call_expr (last inputExprs))
                    place_e' = replaceFunExpr entry_n replace_rec_fun place_e

                    ideal_e' = renameVars ideal_n ideal_ret_n ideal_e
                    eenv' = E.insert ideal_ret_n ideal_e' eenv
                    in
                (s { expr_env = E.insert placeholder_ret_n entry_e
                                $ E.insert placeholder_n place_e' eenv' }, ng')
            | otherwise = (s, ng)

        replaceFunExpr :: Name -> Expr -> Expr -> Expr
        replaceFunExpr n e (Lam u i e') = Lam u i (replaceFunExpr n e e')
        replaceFunExpr n e v@(Var (Id n' _)) = (if n == n' then e else v)
        replaceFunExpr n e (Case b i@(Id n' _) t as) | n == n' = Case (replaceFunExpr n e b) i t as
        replaceFunExpr n e (Case b i t as) = Case (replaceFunExpr n e b) i t (map (\a@(Alt m e') -> Alt m (replaceFunExpr n e e')) as)
        replaceFunExpr n e (Tick t e') = Tick t (replaceFunExpr n e e')
        replaceFunExpr n e (App e' e'') = App (replaceFunExpr n e e') (replaceFunExpr n e e'')
        replaceFunExpr n e (Let b e') = Let (map (\(i, e'') -> (i, replaceFunExpr n e e'')) b) (replaceFunExpr n e e')
        replaceFunExpr n e e' = replaceVar n e e'             

setUpVerification :: Name -> State t -> State t
setUpVerification entry_n s@(State { expr_env = eenv, known_values = kv  })
    | Just entry_e <- E.lookup entry_n eenv
    , Just (smt_n, _) <- E.lookupNameMod (smtName $ nameOcc entry_n) (Just "Spec") eenv
    , Just (placeholder_n, place_e) <- E.lookupNameMod "placeholder" (Just "Spec") eenv
    ,  Just (placeholder_ret_n, _) <- E.lookupNameMod "placeholderRet" (Just "Spec") eenv =
        let place_e' = renameVars entry_n smt_n place_e in
        s { expr_env = E.insert placeholder_ret_n entry_e
                     $ E.insert placeholder_n place_e' eenv
          , known_values = addSmtStringFunc smt_n kv }
    | otherwise = s

smtNameWrap :: T.Text -> T.Text
smtNameWrap n | Just (c, _) <- T.uncons n
              , isAlpha c = n
              | otherwise = "(" <> n <> ")"

smtName :: T.Text -> T.Text
smtName n | Just (c, _) <- T.uncons n
          , isAlpha c = "smt_" <> n
          | otherwise = "$!+$" <> n

setupSpecFuncOrSMT :: [FilePath] -> T.Text -> SynthConfig -> Handle -> Maybe (State t, Id, String, String) -> IO ()
setupSpecFuncOrSMT src f sc h smt_def = case specs_type sc of
                                    SMTFunc -> setUpSpecSMT sc h smt_def
                                    FuncSpecs -> setUpSpecFunc src f sc h smt_def

setUpSpecSMT :: SynthConfig -> Handle -> Maybe (State t, Id, String, String) -> IO ()
setUpSpecSMT _ h Nothing = hClose h
setUpSpecSMT sc h (Just (s@(State { known_values = kv, type_classes = tc }), Id n t, spec,_))  = do
    let ts = splitTyFuns
           . snd
           $ splitTyForAlls t
        t' = foldr1 TyFun
           $ filter (not . isCallStack) ts
        t_with_cs = foldr1 TyFun ts
        vs = take (length (filter (not . isTypeClass tc) . filter (not . isCallStack) $ ts) - 1) argList
        vs_str = intercalate " " vs
        smt_name = T.unpack . smtNameWrap . smtName $ nameOcc n
        eq_ch = case eq_check sc of
                    "==" -> "(==)"
                    x:_ | isAlphaNum x -> "(liftEq " ++ eq_check sc ++ ")"
                    _ -> "(liftEq (" ++ eq_check sc ++ "))"

        placeHolderRet | checking sc == Verify =
            "placeholderRet" ++ " :: " ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t_with_cs) ++ "\n"
                         ++ "placeholderRet = undefined\n\n"
                       | otherwise = "" 
        retVal | checking sc == Verify = "(placeholderRet " ++ vs_str ++ ")"
               | otherwise = "val"

        contents = getImportStr
                    ++ fromMaybe "\n" (fmap (\f -> "import " ++ f ++ "\n") . fmap (dropExtension . takeFileName) $ eq_file sc)
                    ++ "\n"
                    ++ getExcepHandlStr
                    ++ smt_name ++ " :: " ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t') ++ "\n"
                    ++ spec
                    ++ "\n\nplaceholder" ++ " :: " ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t_with_cs) ++ "\n"
                    ++ "placeholder = undefined\n\n"
                    ++ placeHolderRet
                    ++ "comp " ++ vs_str ++ " = " ++ "\n    let val = placeholder " ++ vs_str ++
                            "; cond = " ++ eq_ch ++ " (tryMaybeUnsafe (" ++ smt_name ++ " " ++ vs_str ++ ")) (tryMaybeUnsafe val)" ++ " in\n"
                                                   ++ " case cond of True -> val; False -> assert False " ++ retVal
    putStrLn contents
    hPutStrLn h contents
    hFlush h
    hClose h

-- If generating specification for library functions
setUpSpecFunc :: [FilePath] -> T.Text -> SynthConfig -> Handle -> Maybe (State t, Id, String, String) -> IO ()
setUpSpecFunc src f sc@(SynthConfig { g2_config = config }) h Nothing = do
    proj <- case src of
                src':_ -> guessProj (includePaths config) src'
                _ -> return []

    (s@(State { known_values = kv, type_classes = tc }), func@(Id n ty), _, _) <- initialStateFromFile proj src
                                    Nothing False f (mkCurrExpr TV.empty Nothing Nothing) (mkArgTys config TV.empty)
                                    simplTranslationConfig config
    let ts = splitTyFuns
           . snd
           $ splitTyForAlls ty
        ts_with_bool = ts ++ [tyBool kv]
        t' = foldr1 TyFun
           $ filter (not . isCallStack) ts_with_bool
        t_with_cs = foldr1 TyFun ts
        vs = take (length (filter (not . isTypeClass tc) . filter (not . isCallStack) $ ts_with_bool) - 1) argList
        vs_input = intercalate " " (init vs)
        vs_str = intercalate " " vs
        idealFunName = "ideal_" ++ T.unpack (nameOcc n)

        placeHolderRet | checking sc == Verify =
            "placeholderRet" ++ " :: " ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t_with_cs) ++ "\n"
                         ++ "placeholderRet = undefined\n\n"
                       | otherwise = ""

        idealFuncRet | checking sc == Verify =
            "idealRet" ++ " :: " ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t') ++ "\n"
                         ++ "idealRet = undefined\n\n"
                       | otherwise = "" 

        contents = getImportStr
                    ++ fromMaybe "\n" (fmap (\f -> "import " ++ f ++ "\n") . fmap (dropExtension . takeFileName) $ eq_file sc)
                    ++ "\n"
                    ++ "\n"++ idealFunName ++ " :: " ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t') ++ "\n"
                    ++ idealFunName ++ " " ++ vs_str ++ " = (placeholder " ++ vs_input ++ ") == " ++ last vs
                    ++ "\n\n" ++ idealFuncRet
                    ++ "\n\nplaceholder" ++ " :: " ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t_with_cs) ++ "\n"
                    ++ "placeholder = undefined\n\n"
                    ++ placeHolderRet
                    ++ "comp" ++ " :: " ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t') ++ "\n"
                    ++ "comp " ++ vs_str ++ " = " ++ idealFunName ++ " " ++ vs_str
    putStrLn contents
    hPutStrLn h contents
    hFlush h
    hClose h

    
setUpSpecFunc _ _ sc h (Just (s@(State { known_values = kv, type_classes = tc }), Id n t, spec, _)) = do
    let ts = splitTyFuns
           . snd
           $ splitTyForAlls t
        
        t' = foldr1 TyFun
           $ filter (not . isCallStack) ts
        t_with_cs = foldr1 TyFun ts

        ts_witout_last = init ts
        ts_witout_last' = foldr1 TyFun
           $ filter (not . isCallStack) ts_witout_last
        ts_witout_last'' = foldr1 TyFun ts_witout_last

        vs = take (length (filter (not . isTypeClass tc) . filter (not . isCallStack) $ ts) - 1) argList
        vs_input = intercalate " " (init vs)
        vs_str = intercalate " " vs
        funcSpecName = T.unpack . smtNameWrap . smtName $ nameOcc n
        idealFunName = "ideal_" ++ T.unpack (nameOcc n)

        placeHolderRet | checking sc == Verify =
            "placeholderRet" ++ " :: " ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t_with_cs) ++ "\n"
                         ++ "placeholderRet = undefined\n"
                       | otherwise = ""

        idealFuncRet | checking sc == Verify =
            "idealRet" ++ " :: " ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t') ++ "\n"
                         ++ "idealRet = undefined\n"
                       | otherwise = ""

        val | checking sc == Verify = "idealRet"
               | otherwise = idealFunName        

        contents = getImportStr
                    ++ fromMaybe "\n" (fmap (\f -> "import " ++ f ++ "\n") . fmap (dropExtension . takeFileName) $ eq_file sc)
                    ++ "\n"
                    ++ funcSpecName ++ " :: " ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t') ++ "\n"
                    ++ spec
                    ++ "\n\n"++ idealFunName ++ " :: " ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t') ++ "\n"
                    ++ idealFunName ++ " " ++ vs_str ++ " = (placeholder " ++ vs_input ++ ") == " ++ last vs
                    ++ "\n\n" ++ idealFuncRet
                    ++ "\n\nplaceholder" ++ " :: " ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) ts_witout_last'') ++ "\n"
                    ++ "placeholder = undefined\n\n"
                    ++ placeHolderRet
                    ++ "\n\ncomp" ++ " :: " ++ T.unpack (mkTypeHaskellDictArrows (mkPrettyGuide ()) (type_classes s) t') ++ "\n"
                    ++ "comp " ++ vs_str ++ " = let x = (" ++ funcSpecName ++ " " ++ vs_str ++ ") == (" ++ idealFunName ++ " " ++ vs_str 
                    ++ ") in assert x (" ++ val ++ " " ++ vs_str ++ ")"
    putStrLn contents
    hPutStrLn h contents
    hFlush h
    hClose h

getImportStr :: String
getImportStr = "{-# LANGUAGE BangPatterns, MagicHash, ScopedTypeVariables, ViewPatterns #-}\nmodule Spec where\nimport GHC.Prim2\n"
                    ++ "import GHC.Types2\n"
                    ++ "import GHC.Stack\n"
                    ++ "import Control.Exception\n"
                    ++ "import Data.Functor.Classes\n"
                    ++ "import System.IO.Unsafe\n"

getExcepHandlStr :: String
getExcepHandlStr = "tryMaybe :: IO a -> IO (Maybe a)\n"
                    ++ "tryMaybe a = catch (a >>= \\v -> return (Just v)) (\\(e :: SomeException) -> return Nothing)\n\n"
                    ++ "tryMaybeUnsafe :: a -> Maybe a\n"
                    ++ "tryMaybeUnsafe x = unsafePerformIO $ tryMaybe (let !y = x in return y)\n\n"

isCallStack :: Type -> Bool
isCallStack ty | TyCon tn _:_ <- unTyApp ty = nameOcc tn == "IP"
               | otherwise = False

-- | Find inputs that violate a found SMT definition
findInconsistent :: Id -> State t -> Bindings -> Bool -> State t
findInconsistent entry_f s@(State { expr_env = eenv  }) b output_true
    | Just (ph_name, _) <- E.lookupNameMod "placeholder" (Just "Spec") eenv 
    , Just entry_e <- E.lookup (idName entry_f) eenv =
        s { expr_env = E.insert ph_name entry_e eenv
          , true_assert = output_true }
    | otherwise = error $ "findInconsistent: spec not found"

-------------------------------------------------------------------------------
-- Calling/reading from SyGuS solver
-------------------------------------------------------------------------------
synthFunc :: [ExecRes t] -> SynthConfig -> Maybe String -> Maybe Bool ->  IO (Maybe (SmtCmd, String))
synthFunc er sc smt_def is_spec_correct = do
    cmds <- sygusCmds er sc smt_def is_spec_correct
    runSygus cmds sc

runSygus :: [Cmd] -> SynthConfig -> IO (Maybe (SmtCmd, String))
runSygus sygus_cmds sc = do
    (h_in, h_out, _) <- getCVC5Sygus 60
    mapM_ (\c -> do
            T.hPutStrLn h_in $ printSygus c
            T.putStrLn $ printSygus c
        ) sygus_cmds
    got_input <- hWaitForInput h_out (timeout sc)
    putStrLn $ "HERE " ++ show got_input
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
        [SmtCmd def_fun] -> return $ Just (def_fun, out)
        _ -> return Nothing

sygusCmds :: [ExecRes t] -> SynthConfig -> Maybe String -> Maybe Bool -> IO [Cmd]
sygusCmds [] _ _ _ = return []
sygusCmds er@(ExecRes { final_state = s@(State { tyvar_env = tv_env, known_values = kv }), conc_args = args, conc_out = out_e}:_) 
            sc smt_def is_spec_correct = do
    let define_eq n srt = SmtCmd $ DefineFun n
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

    constraints <- case specs_type sc of
            FuncSpecs -> constraintsForFuncSpec smt_def is_spec_correct er
            SMTFunc -> return $ map execResToConstraints er

    let cmds = [ SmtCmd $ SetLogic "ALL"
            , define_eq "strEq" strSort
            , define_eq "seqIntEq" seq_int_sort
            , define_eq "seqFloatEq" seq_float_sort
            , define_eq "intEq" intSort
            , define_eq "floatEq" floatSort
            , from_char
            , to_char
            , SynthFun "spec" arg_vars ret_sort (Just grm) ] 
            ++ constraints
            -- ++ funcSpecConstraint
            ++ [CheckSynth]
    return cmds
    where
        -- funcSpecConstraint = let
        --                         existsConstraint = TermExists existSortVars existsTerm
        --                         existsTerm = TermCall (ISymb "=") [TermCall (ISymb "spec") (map (TermIdent . ISymb ) (newVars (length args_sort))), exprToTerm kv (mkBool kv False)]
        --                         existSortVars = zipWith SortedVar (newVars (length args_sort)) args_sort
        --                     in 
        --                         if specs_type sc == FuncSpecs then [Constraint existsConstraint] else []

        -- newVars n = ["a" ++ show i | i <- [1..n]]
        -- -- synthFun specname grm = case specs_type sc of
        -- --                 FuncSpecs -> SynthFun specname arg_vars ret_sort_func_spec (Just grm)
        -- --                 SMTFunc -> SynthFun specname arg_vars ret_sort (Just grm)

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
                    , GBfTerm (BfIdentifierBfs (ISymb "str.replace_all") [ strIdent, strIdent, strIdent])
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
                   ]

        grmBool = [ GBfTerm (BfIdentifierBfs (ISymb "ite") [ boolIdent, boolIdent, boolIdent])
                  , GBfTerm (BfIdentifierBfs (ISymb "and") [ boolIdent, boolIdent])
                  , GBfTerm (BfIdentifierBfs (ISymb "or") [ boolIdent, boolIdent])
                  , GBfTerm (BfIdentifierBfs (ISymb "not") [ boolIdent ])

                  , GBfTerm (BfIdentifierBfs (ISymb "intEq") [ intIdent, intIdent ])
                  , GBfTerm (BfIdentifierBfs (ISymb "str.<") [ strIdent, strIdent ])
                  , GBfTerm (BfIdentifierBfs (ISymb "str.<=") [ strIdent, strIdent ])
                  ]
                  ++ boolOpForIdent "strEq" strIdent
                  ++ boolOpForIdent "seqIntEq" seqIntIdent
                  ++ boolOpForIdent "seqFloatEq" seqFloatIdent
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

        ty_gram_defs = (if ret_type == tyChar kv then (([tyChar kv], GroupedRuleList "CharRetPr" strSort grmCharRet):) else id) $
                       (if not (null char_args) then (([tyChar kv], GroupedRuleList "CharArgPr" strSort grmCharArgs):) else id)           
                       [ ([tyString kv], GroupedRuleList "StrPr" strSort grmString)
                       , ([TyApp (tyList kv) (tyInt kv), TyApp (tyList kv) (tyInteger kv)], GroupedRuleList "SeqIntPr" seq_int_sort (grmSeq seq_int_sort seqIntIdent))
                       , ([TyApp (tyList kv) (tyFloat kv)], GroupedRuleList "SeqFloatPr" seq_float_sort (grmSeq seq_float_sort seqFloatIdent))
                       , ([TyLitInt], GroupedRuleList "IntPr" intSort grmInt)
                       , ([TyLitFloat], GroupedRuleList "FloatPr" floatSort grmFloat)
                       , ([tyBool kv], GroupedRuleList "BoolPr" boolSort grmBool)]
        find_start_gram = findElem (\(ty, _) -> ret_type `elem` ty) (if specs_type sc == SMTFunc then ty_gram_defs else funcDefGrammer)
        gram_defs' = case find_start_gram of
                            Just (start_sym, other_sym) -> map snd $ start_sym:other_sym
                            Nothing -> error "runSygus: no start symbol"
        pre_dec = map (\(GroupedRuleList n srt _) -> SortedVar n srt) gram_defs'

        funcDefGrammer =  [ ([tyString kv], GroupedRuleList "StrPr" strSort (map (GBfTerm . BfIdentifier . ISymb) str_args))
                            , ([TyLitInt], GroupedRuleList "IntPr" intSort 
                                [ GVariable intSort
                                    , GBfTerm (BfLiteral (LitNum 0))
                                    , GBfTerm (BfLiteral (LitNum 1))
                                    , GBfTerm (BfLiteral (LitNum 2))
                                    , GBfTerm (BfIdentifierBfs (ISymb "-") [ intIdent, intIdent])
                                    , GBfTerm (BfIdentifierBfs (ISymb "*") [ intIdent, intIdent])
                                    , GBfTerm (BfIdentifierBfs (ISymb "seq.len") [ strIdent ])])
                            , ([tyBool kv], GroupedRuleList "BoolPr" boolSort 
                                [ GBfTerm (BfIdentifierBfs (ISymb "ite") [ boolIdent, boolIdent, boolIdent])
                                    , GBfTerm (BfIdentifierBfs (ISymb "and") [ boolIdent, boolIdent])
                                    , GBfTerm (BfIdentifierBfs (ISymb "<") [ intIdent, intIdent])])
                        ]

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
execResToConstraints er = Constraint $ getTermCallForEq er

getTermCallForEq :: ExecRes t -> Term
getTermCallForEq (ExecRes { final_state = s, conc_args = ars, conc_out = out_e }) =
    let 
        kv = known_values s
        call = TermCall (ISymb "spec") (map (exprToTerm kv) $ relArgs s ars)
        out_t = exprToTerm kv out_e
        termCall = TermCall (ISymb "=") [call, out_t]
    in 
        termCall

constraintsForFuncSpec :: Maybe String -> Maybe Bool -> [ExecRes t] -> IO [Cmd]
constraintsForFuncSpec _ _ [] = return []
constraintsForFuncSpec  smt_def is_spec_correct ers = do
    let (falseErs, trueErs) = getTrueFalseErs [] [] ers
    (falseErs', trueErs') <- (case smt_def of
        -- If specification is correct only then move false ers from disjunction to conjuction
                                Just smt_spec | Just True <- is_spec_correct -> do 
                                    (f, t) <- separateConjDis falseErs smt_spec [] [] 
                                    return (f, trueErs ++ t)
                                _ -> return (falseErs, trueErs))
    let trueCmds = map execResToConstraints trueErs'
    let falseCmds = Constraint $ TermCall (ISymb "or") (map getTermCallForEq falseErs') 
    return (trueCmds ++ [falseCmds])
    
    where
        getTrueFalseErs seenFalse seenTrue [] = (seenFalse, seenTrue)
        getTrueFalseErs seenFalse seenTrue (er@(ExecRes { final_state = s, conc_out = out_e }):es) = 
            if out_e == mkTrue (known_values s) 
            then getTrueFalseErs seenFalse (er:seenTrue) es
            else getTrueFalseErs (er:seenFalse) seenTrue es

        separateConjDis [] _ movables non_movables = return (non_movables, movables)
        separateConjDis (er:es) prev_spec movables non_movables = do
            isMovable <- moveSpecToConjunction prev_spec er
            if isMovable
            then separateConjDis es prev_spec (er:movables ) non_movables
            else separateConjDis es prev_spec movables (er:non_movables)

        moveSpecToConjunction :: String -> ExecRes t -> IO Bool
        moveSpecToConjunction past_spec er = do
            let term = getTermCallForEq er
                assertSt = "( assert " ++ T.unpack (printSygus term) ++ ")"
                cmd = [T.unpack (printSygus (SmtCmd $ SetLogic "ALL")), init (tail past_spec), assertSt, "(check-sat)"]
            (h_in, h_out, _) <- getCVC5ProcessHandles Nothing 60
            mapM_ (\c -> do
                    T.hPutStrLn h_in (T.pack c)
                    T.putStrLn (T.pack c)
                ) cmd
            _ <- hWaitForInput h_out 60
            
            out <- getLinesMatchParens h_out
            _ <- evaluate (length out)
            putStrLn out
            T.hPutStrLn h_in "(exit)"
            
            case out of
                "sat" -> return True
                _ -> return False

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
        conv "str.replace_all" = "strReplaceAll#"
        conv "strEq" = "strEq#"

        conv "seq.++" = "strAppend#"
        conv "seq.len" = "strLen#"
        conv "seq.at" = "strAt#"
        conv "seq.extract" = "strSubstr#"
        conv "seq.prefixof" = "strPrefixOf#"
        conv "seq.suffixof" = "strSuffixOf#"
        conv "seq.contains" = "strContains#"
        conv "seq.indexof" = "strIndexOf#"
        conv "seq.replace" = "strReplace#"
        conv "seq.replace_all" = "strReplaceAll#"
        conv "seqIntEq" = "strEq#"
        conv "seqFloatEq" = "strEq#"

        conv "intEq" = "($==#)"
        conv "floatEq" = "smtEqFloat#"
        conv "fromChar" = ""
        conv "toChar" = ""
        conv "+" = "(+#)"
        conv "-" = "(-#)"
        conv "*" = "(*#)"
        conv "<" = "($<#)"
        conv "ite" = ""
        conv "and" = "(&&)"
        conv "or" = "(||)"
        conv "not" = "not"

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

