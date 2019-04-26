{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module G2.QuasiQuotes.QuasiQuotes (g2) where

import G2.Config
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

import Control.Monad

import Data.Data
import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax as TH
import Language.Haskell.TH.Quote

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
    -- Get names for the lambdas for the regular inputs

    (xs, b) <- parseHaskellQ' str

    let (xs'@(s:_), b') = elimUnused xs b

    let regs = grabRegVars str
        symbs = grabSymbVars str

    ns <- mapM newName regs
    let ns_pat = map varP ns

    let xs'' = addRegVarPasses ns xs' b'

        b'' = b' { input_names = drop (length regs) (input_names b') }
        sol = solveStates xs'' b''
        ars = extractArgs (inputIds s b'') (cleaned_names b'') (type_env s) sol

    foldr (\n -> lamE [n]) ars ns_pat

liftDataT :: Data a => a -> Q Exp
liftDataT = dataToExpQ (\a -> liftText <$> cast a)
    where
        liftText txt = AppE (VarE 'T.pack) <$> lift (T.unpack txt)

parseHaskellQ' :: String -> Q ([State ()], Bindings)
parseHaskellQ' s = do
    ms <- reifyModule =<< thisModule
    runIO $ parseHaskellIO s

-- | Turn the Haskell into a G2 Expr.  All variables- both those that the user
-- marked to be passed into the Expr as real values, and those that the user
-- wants to solve for- are treated as symbolic here.
parseHaskellIO :: String -> IO ([State ()], Bindings)
parseHaskellIO str = do
    (_, exG2) <- withSystemTempFile "ThTemp.hs"
            (\filepath handle -> do
                hPutStrLn handle $ "module ThTemp where\ng2Expr = " ++ subSymb str
                hFlush handle
                hClose handle
                translateLoaded (takeDirectory filepath) filepath []
                    simplTranslationConfig mkConfigDef)
  
    let (s, _, b) = initState' exG2 "g2Expr" (Just "ThTemp") (mkCurrExpr Nothing Nothing) mkConfigDef
        (s', b') = addAssume s b
    
    SomeSolver con <- initSolver mkConfigDef
    case initRedHaltOrd con mkConfigDef of
        (SomeReducer red, SomeHalter hal, SomeOrderer ord) -> do
            xsb@(xs, b) <- runG2ThroughExecution red hal ord [] s' b'

            let xs' = filter (trueCurrExpr) xs

            return (xs', b)
    where
        trueCurrExpr (State { curr_expr = CurrExpr _ e
                            , known_values = kv }) = e == mkTrue kv
        _ = False

addAssume :: State t -> Bindings -> (State t, Bindings)
addAssume s@(State { curr_expr = CurrExpr er e }) b@(Bindings { name_gen = ng }) =
    let
        (v, ng') = freshId (Ty.typeOf e) ng
        e' = Let [(v, e)] (Assume Nothing (Var v) (Var v))
    in
    (s { curr_expr = CurrExpr er e' }, b { name_gen = ng' })

-- | Adds the appropriate number of lambda bindings to the Exp,
-- and sets up a conversion from TH Exp's to G2 Expr's.
-- The returned Exp should have a function type and return type (State t).
addRegVarPasses :: Data t => [TH.Name] -> [State t] -> Bindings -> Q Exp
addRegVarPasses ns xs@(s:_) b@(Bindings { input_names = is, cleaned_names = cleaned }) = do
    let ns_exp = map varE ns
        ty_ns_exp = map (\(n, i) -> sigE n (toTHType cleaned (Ty.typeOf i))) $ zip ns_exp (inputIds s b)

    tenv_name <- newName "tenv"

    let is_exp = liftDataT is

        xs_exp = liftDataT xs

        tenv_exp = liftDataT (type_env s)

        cleaned_exp = liftDataT cleaned

        g2Rep_exp = appE (appE (varE 'g2Rep) (varE tenv_name)) cleaned_exp
        ns_expr = map (appE g2Rep_exp) ty_ns_exp

        zip_exp = appE (appE (varE 'zip) is_exp) $ listE ns_expr
        flooded_exp = appE (varE 'mapMaybe) (appE (varE 'floodConstantsChecking) zip_exp)

        flooded_states = appE flooded_exp xs_exp

    letE [valD (varP tenv_name) (normalB tenv_exp) []] flooded_states
addRegVarPasses _ _ _ = error "QuasiQuoter: No valid solutions found"

elimUnused :: Named t => [State t] -> Bindings -> ([State t], Bindings)
elimUnused xs b =
    let
        b' = b { deepseq_walkers = M.empty
               , higher_order_inst = [] }

        xs' = map (\s -> s { type_classes = initTypeClasses []
                           , rules = [] }) xs
        xs'' = map (fst . flip markAndSweepIgnoringKnownValues b') xs'
    in
    (xs'', b')

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
    in do
    mapM_ (\i -> do
            runIO $ print (Ty.typeOf i)
            th_ty <- toTHType cleaned (Ty.typeOf i)
            runIO $ print $ th_ty ) in_ids
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
        -- (tupE $ map (\(i, n') -> [| g2UnRep $(tenv_exp) ($(varE lst) !! n') |]) $ zip in_ids ([0..] :: [Int]))
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