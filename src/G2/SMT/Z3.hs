{-# LANGUAGE FlexibleContexts #-}

module G2.SMT.Z3 ( printModel
                 , modelToIOString
                 , reachabilitySolverZ3
                 , outputSolverZ3) where

import G2.Core.CoreManipulator as Man
import G2.Core.Language
import G2.Core.Evaluator
import qualified G2.Core.Utils as Utils
import G2.Haskell.Prelude
import G2.SMT.Z3Types

import Control.Monad

import Data.Semigroup.Monad

import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Ord

import qualified Data.Set as S

import Z3.Monad

import Data.Ratio

import qualified Debug.Trace as T

--This function is just kind of a hack for now... might want something else later?
printModel :: (State -> Z3 (Result, Maybe Model)) -> State -> IO ()
printModel f s = do
    (r, m) <- evalZ3 . f $ s
    m' <- case m of Just m'' -> modelToIOString m''
                    Nothing -> return ""

    print r
    putStrLn m'

modelToIOString :: Model -> IO (String)
modelToIOString m = evalZ3 . modelToString $ m

--Use the SMT solver to find inputs that will reach the given state
--(or determine that it is not possible to reach the state)
reachabilitySolverZ3 :: State -> Z3 (Result, Maybe Model)
reachabilitySolverZ3 s@State {tEnv = tv, pc = pc'} = do
    dtMap <- mkDatatypesZ3 tv
    
    handleExprEnv dtMap s

    mapM assert =<< constraintsZ3 dtMap pc'

    setASTPrintMode Z3_PRINT_SMTLIB2_COMPLIANT
    s' <- solverToString
    T.trace s' solverCheckAndGetModel 

--Use the SMT solver to attempt to find inputs that will result in output
--satisfying the given curr expr
outputSolverZ3 :: State -> Z3 (Result, Maybe Model)
outputSolverZ3 s@State{tEnv = tv, cExpr = expr, pc = pc'}  = do
    dtMap <- mkDatatypesZ3 tv

    handleExprEnv dtMap s

    assert =<< exprZ3 dtMap M.empty expr
    mapM assert =<< constraintsZ3 dtMap pc'

    setASTPrintMode Z3_PRINT_SMTLIB2_COMPLIANT
    s' <- solverToString
    T.trace s' solverCheckAndGetModel

constraintsZ3 :: TypeMaps -> PC -> Z3 [AST]
constraintsZ3 d (pc) = do
    mapM (constraintsZ3' d) pc
    where
        constraintsZ3' :: TypeMaps -> (Expr, Alt, Bool) -> Z3 AST
        constraintsZ3' d (expr, alt, b) = do
            e <- exprZ3 d M.empty expr
            a <- altZ3 d M.empty alt

            if b then mkEq e a else mkNot =<< mkEq e a

--Searches the current expression and path constraints
--for references to the expression enviroment
--If any exist, sets variables accordingly
handleExprEnv :: TypeMaps -> State -> Z3 ()
handleExprEnv d State {eEnv = eexpr, cExpr = curr_expr, pc = pc'} = do
    getMon . Man.eval (handleExprEnv' d eexpr) $ curr_expr
    getMon . Man.eval (handleExprEnv' d eexpr) $ pc'
    where
        handleExprEnv' :: TypeMaps -> EEnv -> Expr -> Mon Z3 ()
        handleExprEnv' d eenv (Var n t) =
            case M.lookup n eenv of
                Just e -> if length (fst . Utils.unlam $ e) > 0 then Mon . createEnvFunc d n t $ e else return ()
                Nothing -> return ()
        handleExprEnv' _ _ _ = return ()

        createEnvFunc :: TypeMaps -> Name -> Type -> Expr -> Z3 ()
        createEnvFunc d n t e = do
            let (nt, e') = Utils.unlam e
            
            n' <- mapM (mkStringSymbol . fst) nt
            t' <- mapM (sortZ3 d . snd) nt

            n'' <- mapM (\(_n, _t) -> exprZ3 d M.empty (Var _n _t)) nt

            fd <- mkFuncDeclZ3 d n t

            app <- mkApp fd n''
            
            eq <- mkEq app =<< exprZ3 d M.empty e'
            assert =<< mkForall [] n' t' eq

exprZ3 :: TypeMaps -> M.Map Name AST -> Expr -> Z3 AST
exprZ3 _ _ (Var "True" _) = mkTrue
exprZ3 _ _ (Var "False" _) = mkFalse
exprZ3 d m (Var v t)
    | Just c <- M.lookup v (consFuncs d) = mkApp c []
    | Just a <- M.lookup v m = return a
    | otherwise = do
                    v' <- mkStringSymbol v
                    t' <- sortZ3 d t
                    mkVar v' t'
exprZ3 _ _ (Const c) = constZ3 c
exprZ3 d m a@(App _ _) =
    let
        func = fromJust . Utils.getAppFunc $ a
        args = Utils.getAppArgs a
    in
    handleFunctionsZ3 d m func args
exprZ3 d m c@(Case e ae t) = do
    e' <- exprZ3 d m e

    mkIteAltExpr =<< mapM (exprZ3AltExpr d m e') ae
    where
        {- TypeMaps
            -> Functions
            -> the expression being evaluated
            -> an alt, expr pair
            -> (a recognizer, an expression for if that recognizer is true)
        -}
        exprZ3AltExpr :: TypeMaps -> M.Map Name AST -> AST -> (Alt, Expr) -> Z3 (AST, AST)
        exprZ3AltExpr tm m e ae@(alt@(Alt (DC (n, _, t, ts), n')), e') = do
            accApp <- case M.lookup n . accessorFuncs $ tm of
                                Just a -> mapM (\a' -> mkApp a' [e]) a --a
                                Nothing -> accDefault n e alt

            if length accApp == length n' then
                do
                    recApp <- case M.lookup n . recFuncs $ tm of
                                Just r -> mkApp r [e]
                                Nothing -> recDefault n e alt

                    --accApp <- mapM (\a -> mkApp a [e]) acc

                    let accAppMap = M.fromList . zip n' $ accApp
                    e'' <- exprZ3 tm (M.union accAppMap m) e'

                    return (recApp, e'')
            else
                error ("Too many arguments in case with " ++ show ae)

        mkIteAltExpr :: [(AST, AST)] -> Z3 AST
        mkIteAltExpr ((_, e):[]) = return e
        mkIteAltExpr ((r, e):es) = mkIte r e =<< mkIteAltExpr es

        accDefault :: Name -> AST -> Alt -> Z3 [AST]
        accDefault _ e (Alt (DC ("True", _, _, _), _)) = return []
        accDefault _ e (Alt (DC ("False", _, _, _), _)) = return []
        accDefault _ e (Alt (DC ("D#", _, _, _), [d])) = return [e]
        accDefault _ e (Alt (DC ("F#", _, _, _), [f])) = return [e]
        accDefault _ e (Alt (DC ("I#", _, _, _), [i])) = return [e]
        accDefault n _ _ = error ("No accessor functions for " ++ n ++ " in exprZ3AltExpr")

        recDefault :: Name -> AST -> Alt -> Z3 AST
        recDefault _ e (Alt (DC ("True", _, _, _), _)) = mkEq e =<< mkTrue
        recDefault _ e (Alt (DC ("False", _, _, _), _)) = mkEq e =<< mkFalse
        recDefault _ e (Alt (DC ("D#", _, _, _), _)) = mkTrue
        recDefault _ e (Alt (DC ("F#", _, _, _), _)) = mkTrue
        recDefault _ e (Alt (DC ("I#", _, _, _), _)) = mkTrue
        recDefault n _ _ = error ("No recognizer functions for " ++ n ++ " in exprZ3AltExpr")

exprZ3 _ _ e = error ("Unknown expression " ++ show e ++ " in exprZ3")

handleFunctionsZ3 :: TypeMaps -> M.Map Name AST -> Expr -> [Expr] -> Z3 AST
--Mappings fairly directly from Haskell to SMT
--Need to account for weird user implementations of Num?
handleFunctionsZ3 d m (Var "==" _ ) [_, _, a, b] = do
    a' <- exprZ3 d m a
    b' <- exprZ3 d m b
    mkEq a' b'
handleFunctionsZ3 d m (Var ">" _ ) [_, _, a, b] = do
    a' <- exprZ3 d m a
    b' <- exprZ3 d m b
    mkGt a' b'
handleFunctionsZ3 d m (Var "<" _ ) [_, _, a, b] = do
    a' <- exprZ3 d m a
    b' <- exprZ3 d m b
    mkLt a' b'
handleFunctionsZ3 d m (Var ">=" _ ) [_, _, a, b] = do
    a' <- exprZ3 d m a
    b' <- exprZ3 d m b
    mkGe a' b'
handleFunctionsZ3 d m (Var "<=" _ ) [_, _, a, b] = do
    a' <- exprZ3 d m a
    b' <- exprZ3 d m b
    mkLe a' b'
handleFunctionsZ3 d m (Var "+" _ ) [_, _, a, b] = do
    a' <- exprZ3 d m a
    b' <- exprZ3 d m b
    mkAdd [a', b']
handleFunctionsZ3 d m (Var "-" _ ) [_, _, a, b] = do
    a' <- exprZ3 d m a
    b' <- exprZ3 d m b
    mkSub [a', b']
handleFunctionsZ3 d m (Var "*" _ ) [_, _, a, b] = do
    a' <- exprZ3 d m a
    b' <- exprZ3 d m b
    mkMul [a', b']
handleFunctionsZ3 d m (Var "&&" _ ) [a, b] = do
    a' <- exprZ3 d m a
    b' <- exprZ3 d m b
    mkAnd [a', b']
handleFunctionsZ3 d m (Var "||" _ ) [a, b] = do
    a' <- exprZ3 d m a
    b' <- exprZ3 d m b
    mkOr [a', b']
--Constructors for built in datatypes
handleFunctionsZ3 _ _ (Var "I#" _) [Const c] = constZ3 c
handleFunctionsZ3 d m (Var "I#" _) [e] = exprZ3 d m e
handleFunctionsZ3 _ _ (Var "F#" _) [Const c] = constZ3 c
handleFunctionsZ3 d m (Var "F#" _) [e] = exprZ3 d m e
handleFunctionsZ3 _ _ (Var "D#" _) [Const c] = constZ3 c
handleFunctionsZ3 d m (Var "D#" _) [e] = exprZ3 d m e
handleFunctionsZ3 tm m (Var n t1) e = do
    f <- case M.lookup n (consFuncs tm) of
                Just c -> return c
                Nothing -> mkFuncDeclZ3 tm n t1
    
    e' <- mapM (exprZ3 tm m) e
    mkApp f e'
handleFunctionsZ3 d m (Lam n e t) [e'] = do
    n' <- mkStringSymbol n
    t' <- sortZ3 d . Utils.ithArgType t $ 1
    v <- mkVar n' t'
    e'' <- exprZ3 d m e'
    --Possibly patterns could speed this up?
    assert =<< mkEq v e''--mkForall [] [n'] [t'] =<< exprZ3 d e
    exprZ3 d m e
handleFunctionsZ3 _ _ e _ = error ("Unknown expression " ++ show e ++ " in handleFunctionsZ3")


mkFuncDeclZ3 :: TypeMaps -> Name -> Type -> Z3 FuncDecl
mkFuncDeclZ3 d n t = do
    n' <- mkStringSymbol n

    sorts <- sortFuncZ3 d t
    let (sorts', sort'') = frontLast sorts

    mkFuncDecl n' sorts' sort''
    where
        frontLast :: [a] -> ([a], a)
        frontLast (x:[]) = ([], x)
        frontLast (x:xs) =
            let
                (fl, fl') = frontLast xs
            in
            (x:fl, fl')
        frontLast [] = error "Empty list passed to frontLast in mkFuncDeclZ3."

constZ3 :: Const -> Z3 AST
constZ3 (CInt i) = mkInt i =<< mkIntSort
constZ3 (CFloat r) = mkReal (fromInteger . numerator $ r) (fromInteger . denominator $ r)
constZ3 (CDouble r) = mkReal (fromInteger . numerator $ r) (fromInteger . denominator $ r)


altZ3 :: TypeMaps -> M.Map Name AST -> Alt -> Z3 AST
altZ3 _ _ (Alt (DC ("True", _, TyConApp "Bool" _, _), _)) = mkBool True
altZ3 _ _ (Alt (DC ("False", _, TyConApp "Bool" _, _), _)) = mkBool False
altZ3 _ _ (Alt (DC ("I#", _, TyConApp "Int" _, _), i)) = do
    intSort <- mkIntSort
    case i of
        [i'] -> do
            s <- mkStringSymbol i'
            mkVar s intSort
        otherwise -> mkFreshConst "intCase" intSort
    
altZ3 tm m (Alt (DC (x, _, TyConApp n _, ts), ns)) = do
    let sort = case M.lookup n (types tm) of
                    Just s -> s
                    Nothing -> error ("Type " ++ x ++ " not recognized.")
    cons <- getDatatypeSortConstructors sort

    rel_cons <- filterM (getRelevantCon x) cons
    let rel_con = rel_cons !! 0

    ex <- mapM (exprZ3 tm m) . map (\(n', t') -> Var n' t') . zip ns $ ts

    mkApp rel_con ex
    where
        getRelevantCon :: Name -> FuncDecl -> Z3 Bool
        getRelevantCon n f = do
            n' <- mkStringSymbol n
            f' <- getDeclName f
            return (n' == f')
altZ3 _ _ e = error ("Case of " ++ show e ++ " not handled in altZ3.")