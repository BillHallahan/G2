{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module G2.QuasiQuotes.QuasiQuotes (g2) where

import G2.Config
import G2.Execution.Interface
import G2.Execution.Memory
import G2.Execution.Reducer
import G2.Initialization.MkCurrExpr
import qualified G2.Language.ExprEnv as E
import G2.Interface
import G2.Language as G2
import qualified G2.Language.Typing as Ty
import G2.Solver
import G2.Translation.Interface
import G2.Translation.TransTypes
import G2.QuasiQuotes.FloodConsts
import G2.QuasiQuotes.G2Rep
import G2.QuasiQuotes.Support
import G2.QuasiQuotes.Parser
import G2.QuasiQuotes.ModuleGraphLoader

import Control.Monad

import Data.Data
import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax as TH
import Language.Haskell.TH.Quote

import System.Directory
import System.IO
import System.IO.Temp
import System.FilePath

g2 :: QuasiQuoter
g2 = QuasiQuoter { quoteExp = parseHaskellQ
                 , quotePat = error "g2: No QuasiQuoter for patterns."
                 , quoteType = error "g2: No QuasiQuoter for types."
                 , quoteDec = error "g2: No QuasiQuoter for declarations." }

parseHaskellQ :: String -> Q Exp
parseHaskellQ str = do


    -- runIO $ putStrLn $ "CWD is: " ++ cwd

    -- Get names for the lambdas for the regular inputs
    let qext = extractQuotedData str

    -- let regs = grabRegVars str
    let regs = map fst $ concVars qext

    ns <- mapM newName regs
    let ns_pat = map varP ns

    -- Get names for the lambdas for the regular inputs
    exG2 <- parseHaskellQ' qext
    ex_out <- runExecutionQ exG2

    case ex_out of
        Completed xs b -> do
            case elimUnusedCompleted xs b of
                (xs'@(s:_), b') -> do

                    let xs'' = addCompRegVarPasses ns xs' b'

                        b'' = b' { input_names = drop (length regs) (input_names b') }
                        sol = solveStates xs'' b''
                        ars = extractArgs (inputIds s b'') (cleaned_names b'') (type_env s) sol

                    foldr (\n -> lamE [n]) ars ns_pat
                ([], _) -> foldr (\n -> lamE [n]) [| return Nothing |] ns_pat
        NonCompleted s b -> do
            let (s', b') = elimUnusedNonCompleted s b

                s'' = addedNonCompRegVarBinds ns s' b'

                b'' = b' { input_names = drop (length regs) (input_names b') }

                sol = executeAndSolveStates s'' b''

                ars = extractArgs (inputIds s b'') (cleaned_names b'') (type_env s) sol

            foldr (\n -> lamE [n]) ars ns_pat

            -- foldr (\n -> lamE [n]) [|do putStrLn "NONCOMPLETED"; return Nothing;|] ns_pat

liftDataT :: Data a => a -> Q Exp
liftDataT = dataToExpQ (\a -> liftText <$> cast a)
    where
        liftText txt = AppE (VarE 'T.pack) <$> lift (T.unpack txt)

parseHaskellQ' :: QuotedExtract-> Q ExtractedG2
parseHaskellQ' qext = do
  (ModuleInfo mods) <- reifyModule =<< thisModule
  runIO $ mapM putStrLn =<< guessModules mods
  runIO $ putStrLn "-----"
  runIO $ parseHaskellIO qext

-- | Turn the Haskell into a G2 Expr.  All variables- both those that the user
-- marked to be passed into the Expr as real values, and those that the user
-- wants to solve for- are treated as symbolic here.
parseHaskellIO :: QuotedExtract -> IO ExtractedG2
parseHaskellIO qext = do
    cwd <- getCurrentDirectory
    let cwd' = cwd ++ "/quasiquote/"
    let hskStr = quotedEx2Hsk qext
    (_, exG2) <- withSystemTempFile fileName
            (\filepath handle -> do
                putStrLn hskStr
                hPutStrLn handle $ "module " ++ moduleName ++ " where\n"
                                    ++ "import MiniLib\n"
                                    ++ functionName ++ " = " ++ hskStr
                hFlush handle
                hClose handle
                translateLoaded (takeDirectory filepath) filepath []
                    simplTranslationConfig
                    (mkConfigDef { extraPaths = [cwd'] }))
    return exG2

-- | If a State has been completely symbolically executed (i.e. no states were
-- discarded by a Halter) we encoded it as Completed.
-- Otherwise, we encode the original State and Bindings as NonCompleted
data ExecOut = Completed [State ()] Bindings
             | NonCompleted (State ()) Bindings

runExecutionQ :: ExtractedG2 -> Q ExecOut
runExecutionQ exG2 = runIO $ do
    let (s, _, b) = initState' exG2 (T.pack functionName) (Just $ T.pack moduleName)
                                        (mkCurrExpr Nothing Nothing) mkConfigDef
        (s', b') = addAssume s b
    
    SomeSolver con <- initSolver mkConfigDef
    case qqRedHaltOrd con of
        (SomeReducer red, SomeHalter hal, SomeOrderer ord) -> do
            let (s'', b'') = runG2Pre [] s' b'
                hal' = hal :<~> ZeroHalter 2000
            xsb@(xs, b''') <- runExecutionToProcessed red hal' ord s'' b''

            case xs of
                Processed { accepted = acc, discarded = [] } -> do
                    let acc' = filter (trueCurrExpr) acc
                    return $ Completed acc' b'''
                _ -> return $ NonCompleted s' b'
    where
        trueCurrExpr (State { curr_expr = CurrExpr _ e
                            , known_values = kv }) = e == mkTrue kv
        _ = False

fileName :: String
fileName = "THTemp.hs"

moduleName :: String
moduleName = "THTemp"

functionName :: String
functionName = "g2Expr"

qqRedHaltOrd :: Solver conv => conv -> (SomeReducer (), SomeHalter (), SomeOrderer ())
qqRedHaltOrd conv =
    let
        tr_ng = mkNameGen ()
        state_name = G2.Name "state" Nothing 0 Nothing
    in
    ( SomeReducer
        (NonRedPCRed :<~| TaggerRed state_name tr_ng)
            <~| (SomeReducer (StdRed conv))
    , SomeHalter
        (DiscardIfAcceptedTag state_name 
        :<~> AcceptHalter)
    , SomeOrderer NextOrderer)

addAssume :: State t -> Bindings -> (State t, Bindings)
addAssume s@(State { curr_expr = CurrExpr er e }) b@(Bindings { name_gen = ng }) =
    let
        (v, ng') = freshId (Ty.typeOf e) ng
        e' = Let [(v, e)] (Assume Nothing (Var v) (Var v))
    in
    (s { curr_expr = CurrExpr er e' }, b { name_gen = ng' })

type TypeEnvName = TH.Name

-- Returns an Q Exp represeting a [(Name, Expr)] list
regVarBindings :: [TH.Name] -> TypeEnvName -> InputIds -> Bindings -> Q Exp
regVarBindings ns tenv_name is b@(Bindings { input_names = ins, cleaned_names = cleaned }) = do
    let ns_exp = map varE ns
        ty_ns_exp = map (\(n, i) -> sigE n (toTHType cleaned (Ty.typeOf i))) $ zip ns_exp is

        ins_exp = liftDataT ins

        cleaned_exp = liftDataT cleaned

        g2Rep_exp = [| g2Rep $(varE tenv_name) $(cleaned_exp) |]
        ns_expr = map (appE g2Rep_exp) ty_ns_exp

        zip_exp = [| zip $(ins_exp) $(listE ns_expr) |]
    zip_exp

-- | Adds the appropriate number of lambda bindings to the Exp,
-- and sets up a conversion from TH Exp's to G2 Expr's.
-- The returned Exp should have a function type and return type (State t).
addCompRegVarPasses :: Data t => [TH.Name] -> [State t] -> Bindings -> Q Exp
addCompRegVarPasses ns xs@(s:_) b@(Bindings { input_names = is, cleaned_names = cleaned }) = do
    tenv_name <- newName "tenv"

    let xs_exp = liftDataT xs

        tenv_exp = liftDataT (type_env s)

        zip_exp = regVarBindings ns tenv_name (inputIds s b) b

        flooded_exp = appE (varE 'mapMaybe) (appE (varE 'floodConstantsChecking) zip_exp)

        flooded_states = appE flooded_exp xs_exp

    letE [valD (varP tenv_name) (normalB tenv_exp) []] flooded_states
addCompRegVarPasses _ _ _ = error "QuasiQuoter: No valid solutions found"

addedNonCompRegVarBinds :: Data t => [TH.Name] -> State t -> Bindings -> Q Exp
addedNonCompRegVarBinds ns s b = do
    tenv_name <- newName "tenv"
    let s_exp = liftDataT s
        tenv_exp = liftDataT (type_env s)

        zip_exp = regVarBindings ns tenv_name (inputIds s b) b

        flooded_exp = [| case floodConstantsChecking $(zip_exp) $(s_exp) of
                            Just s -> s
                            Nothing -> error "addedNonCompRegVarBinds: Nothing"|]

    letE [valD (varP tenv_name) (normalB tenv_exp) []] flooded_exp

elimUnusedCompleted :: Named t => [State t] -> Bindings -> ([State t], Bindings)
elimUnusedCompleted xs b =
    let
        b' = b { deepseq_walkers = M.empty
               , higher_order_inst = [] }

        xs' = map (\s -> s { type_classes = initTypeClasses []
                           , rules = [] }) xs
        xs'' = map (fst . flip markAndSweepIgnoringKnownValues b') xs'
    in
    (xs'', b')

elimUnusedNonCompleted :: Named t => State t -> Bindings -> (State t, Bindings)
elimUnusedNonCompleted s b =
    let
        b' = b { deepseq_walkers = M.empty
               , higher_order_inst = [] }
        s' = s { type_classes = initTypeClasses []
               , rules = [] }
    in
    markAndSweepIgnoringKnownValues s' b'

executeAndSolveStates :: Q Exp -> Bindings -> Q Exp
executeAndSolveStates s b = do
    varE 'executeAndSolveStates' `appE` liftDataT b `appE` s 

executeAndSolveStates' :: Bindings -> State () -> IO (Maybe (ExecRes ()))
executeAndSolveStates' b s = do
    SomeSolver con <- initSolver mkConfigDef
    case qqRedHaltOrd con of
        (SomeReducer red, SomeHalter hal, _) -> do
            let hal' = hal :<~> MaxOutputsHalter (Just 1) :<~> SwitchEveryNHalter 2000
            (res, _) <- runG2 red hal' PickLeastUsedOrderer con [] s b
            case res of
                exec_res:_ -> return $ Just exec_res
                _ -> return Nothing

-- Takes an Exp representing a list of States, and returns an Exp representing an ExecRes
solveStates :: Q Exp -> Bindings -> Q Exp
solveStates xs b = do
    varE 'solveStates' `appE` liftDataT b `appE` xs 

solveStates' :: ( Named t
                , ASTContainer t Expr
                , ASTContainer t G2.Type) => Bindings -> [State t] -> IO (Maybe (ExecRes t))
solveStates' b xs = do
    SomeSolver con <- initSolver mkConfigDef
    solveStates'' con b xs

solveStates'' :: ( Named t
                 , ASTContainer t Expr
                 , ASTContainer t G2.Type
                 , Solver sol) => sol -> Bindings -> [State t] -> IO (Maybe (ExecRes t))
solveStates'' _ _ [] =return Nothing
solveStates'' sol b (s:xs) = do
    m_ex_res <- runG2Solving sol b s
    case m_ex_res of
        Just _ -> return m_ex_res
        Nothing -> solveStates'' sol b xs

-- | Get the values of the symbolic arguments, and returns them in a tuple
extractArgs :: InputIds -> CleanedNames -> TypeEnv -> Q Exp -> Q Exp
extractArgs in_ids cleaned tenv es =
    let
        n = length in_ids
    in
    [|do
        r <- $(es)
        case r of
            Just r' ->
                return . Just . $(toSymbArgsTuple in_ids cleaned tenv n) $ conc_args r'
            Nothing -> return Nothing |]

-- | Takes some int n returns a function to turn the first n elements of a list
-- into a tuple
toSymbArgsTuple :: InputIds -> CleanedNames -> TypeEnv -> Int -> Q Exp
toSymbArgsTuple in_ids cleaned tenv n = do
    lst <- newName "lst"

    let tenv_exp = liftDataT tenv

    lamE [varP lst]
        (tupE $ map (\(i, n') -> [| g2UnRep $(tenv_exp) ($(varE lst) !! n') :: $(toTHType cleaned (Ty.typeOf i)) |]) $ zip in_ids ([0..] :: [Int]))

grabRegVars :: String -> [String]
grabRegVars s =
    let
        s' = dropWhile (\c -> c == ' ' || c == '(') s
    in
    case s' of
        '\\':xs -> grabVars "->" xs
        _ -> error "Bad QuasiQuote"

afterRegVars :: String -> String
afterRegVars s = strip s
    where 
        strip ('-':'>':xs) = xs
        strip (_:xs) = strip xs
        strip [] = []

grabSymbVars :: String -> [String]
grabSymbVars s =
    let
        s' = dropWhile (\c -> c == ' ' || c == '(') $ afterRegVars s
    in
    case s' of
        '-':'>':xs -> grabVars "?" xs
        _ -> error "Bad QuasiQuote"

grabVars :: String -> String -> [String]
grabVars _ [] = []
grabVars en (' ':xs) = grabVars en xs
grabVars en xs
    |  take (length en) xs == en = []
grabVars en xs@(_:_) =
    let
        (x, xs') = span (/= ' ') xs
    in
    x:grabVars en xs'

-- | Replaces the first '->' with '-> \' and the first ?' with '->'
subSymb :: String -> String
subSymb = sub
    where
        sub ('-':'>':xs) = '-':'>':' ':'\\':sub xs
        sub ('?':xs) = "->" ++ xs
        sub (x:xs) = x:sub xs
        sub "" = ""
