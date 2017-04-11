{-# LANGUAGE FlexibleContexts #-}

module G2.SMT.Z3 where

import G2.Core.CoreManipulator as Man
import G2.Core.Language
import G2.Core.Evaluator
import G2.Core.Utils
import G2.Haskell.Prelude

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

type ConsFuncDecl = FuncDecl
type RecognizerFuncDecl = FuncDecl
type AccessorFuncDecl = FuncDecl


type TypeMaps = (M.Map Name Sort, M.Map Name (ConsFuncDecl, RecognizerFuncDecl))

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
reachabilitySolverZ3 s@(tv, ev, expr, pc) = do
    dtMap <- mkDatatypesZ3 tv
    
    handleExprEnv dtMap s

    mapM assert =<< constraintsZ3 dtMap pc

    setASTPrintMode Z3_PRINT_SMTLIB2_COMPLIANT
    s' <- solverToString
    T.trace (s') solverCheckAndGetModel 

--Use the SMT solver to attempt to find inputs that will result in output
--satisfying the given curr expr
outputSolverZ3 :: State -> Z3 (Result, Maybe Model)
outputSolverZ3 s@(tv, ev, expr, pc)  = do
    dtMap <- mkDatatypesZ3 tv

    handleExprEnv dtMap s

    assert =<< exprZ3 dtMap expr
    mapM assert =<< constraintsZ3 dtMap pc

    setASTPrintMode Z3_PRINT_SMTLIB2_COMPLIANT
    s' <- solverToString
    T.trace (s') solverCheckAndGetModel

constraintsZ3 :: TypeMaps -> PC -> Z3 [AST]
constraintsZ3 d (pc) = do
    mapM (constraintsZ3' d) pc
    where
        constraintsZ3' :: TypeMaps -> (Expr, Alt, Bool) -> Z3 AST
        constraintsZ3' d (expr, alt, b) = do
            e <- exprZ3 d expr
            a <- altZ3 d alt

            if b then mkEq e a else mkNot =<< mkEq e a

--Searches the current expression and path constraints
--for references to the expression enviroment
--If any exist, sets variables accordingly
handleExprEnv :: TypeMaps -> State -> Z3 ()
handleExprEnv d (_, eexpr, curr_expr, pc) = do
    getMon . Man.eval (handleExprEnv' d eexpr) $ curr_expr
    getMon . Man.eval (handleExprEnv' d eexpr) $ pc
    where
        handleExprEnv' :: TypeMaps -> EEnv -> Expr -> Mon Z3 ()
        handleExprEnv' d eenv (Var n t) =
            case M.lookup n eenv of
                Just e -> if length (fst . unlam $ e) > 0 then Mon . createEnvFunc d n t $ e else return ()
                Nothing -> return ()
        handleExprEnv' _ _ _ = return ()

        createEnvFunc :: TypeMaps -> Name -> Type -> Expr -> Z3 ()
        createEnvFunc d n t e = do
            let (nt, e') = unlam e
            
            n' <- T.trace (n ++ "   " ++ show nt) mapM (mkStringSymbol . fst) nt
            t' <- mapM (sortZ3 d . snd) nt

            n'' <- mapM (\(_n, _t) -> exprZ3 d (Var _n _t)) nt

            fd <- mkFuncDeclZ3 d n t

            app <- T.trace ("createEnvFunc e' = " ++ show e') mkApp fd n''
            
            eq <- mkEq app =<< exprZ3 d e'
            assert =<< mkForall [] n' t' eq

mkDatatypesZ3 :: TEnv -> Z3 TypeMaps
mkDatatypesZ3 tenv = mkSortsZ3 M.empty M.empty
                     . M.toList
                     . M.filterWithKey (\k _  -> not (k `S.member` knownTypes)) $ tenv
    where
        knownTypes = S.fromList . map fst $ prelude_t_decls

        requires :: Type -> [Name]
        requires (TyAlg n1 t1) = 
            catMaybes . map names . concat . map (\(DC (_, _, _, t')) -> t') $ t1
        requires _ = error "Must only pass TyAlg's to requires in mkDatatypesZ3"

        names :: Type -> Maybe Name
        names (TyConApp n _) = Just n 
        names _ = Nothing

        mkSortsZ3 :: M.Map Name Sort -> M.Map Name (ConsFuncDecl, RecognizerFuncDecl) -> [(Name, Type)] -> Z3 TypeMaps
        mkSortsZ3 d c ((n, t@(TyAlg n' dcs)):xs) = do
            let r = requires t

            let (s, s') = partition (\(n'', _) -> n'' `elem` r) xs
            (d', c') <- mkSortsZ3 d c s

            cons <- mapM (mkConstructorZ3 (d', c')) dcs
            nSymb <- mkStringSymbol n
            da <- mkDatatype nSymb (map (fst . snd) cons)
           
            cons' <- getDatatypeSortConstructors da
            rec <- getDatatypeSortRecognizers da
            let funcDecls = zip (map fst cons) (zip cons' rec)

            let c'' = M.union c' (M.fromList $ funcDecls)

            mkSortsZ3 (M.insert n da d') c'' s'
        mkSortsZ3 d c [] = return (d, c)

mkConstructorZ3 :: TypeMaps -> DataCon -> Z3 (Name, (Constructor, [Symbol]))
--we need to do something to ensure all symbols are unique... adjust
mkConstructorZ3 d (DC (n, _, tc, t)) = do
    n' <- mkStringSymbol n
    is_n <- mkStringSymbol ("is_" ++ n)
    s <- mapM mkStringSymbol . numFresh n (length t) $ []
    t' <- mapM (\_t -> if _t /= tc then return .  Just =<< sortZ3 d _t else return  Nothing) t

    cons <- mkConstructor n' is_n . map (\(s, t) -> (s, t, 0)) . zip s $ t'

    return (n, (cons, s))

exprZ3 :: TypeMaps -> Expr -> Z3 AST
exprZ3 _ (Var "True" _) = mkTrue
exprZ3 _ (Var "False" _) = mkFalse
exprZ3 d (Var v t) =
    case M.lookup v (snd d) of
            Just (c, _) -> do
                mkApp c []
            Nothing -> do
                v' <- mkStringSymbol v
                t' <- sortZ3 d t
                mkVar v' t'
exprZ3 _ (Const c) = constZ3 c
exprZ3 d a@(App _ _) =
    let
        func = fromJust . getAppFunc $ a
        args = getAppArgs a
    in
    handleFunctionsZ3 d func args
exprZ3 d c@(Case e ae t) = do
    e' <- exprZ3 d e
    --exprZ3AltExpr d e' ae
    r <- mkFreshConst "case" =<< sortZ3 d t

    assert =<< mkAnd =<< mapM (exprZ3AltExpr'' d e' r) ae
    return r
    where
        {- TypeMaps
            -> the expression being evaluated
            -> the expression to store result
            -> alt, expr pairs
            -> the implies
        -}
        -- exprZ3AltExpr :: TypeMaps -> AST -> [(Alt, Expr)] -> Z3 AST
        -- exprZ3AltExpr d e (ae:[]) = exprZ3AltExpr' d e ae
        -- exprZ3AltExpr d e (ae@(Alt (DC (n, _, _, _)), e'):es) = do
        --     let rec = snd . M.lookup n d

        --     recApp <- mkApp rec e

        --     mkIte recApp =<< exprZ3AltExpr' d e ae =<< exprZ3AltExpr d e es

        -- exprZ3AltExpr' :: TypeMaps -> AST -> (Alt, Expr) -> Z3 AST
        -- exprZ3AltExpr' d e (alt, e') = mkTrue



        exprZ3AltExpr'' :: TypeMaps -> AST -> AST -> (Alt, Expr) -> Z3 AST
        exprZ3AltExpr'' d expr_eq case_eq (_a, _e) = do
            _a' <- altZ3 d _a
            _a_eq <- mkEq _a' expr_eq

            _e' <- exprZ3 d _e
            _e_eq <- mkEq _e' case_eq

            mkImplies _a_eq _e_eq
exprZ3 d e = error ("Unknown expression " ++ show e ++ " in exprZ3")

handleFunctionsZ3 :: TypeMaps -> Expr -> [Expr] -> Z3 AST
--Mappings fairly directly from Haskell to SMT
--Need to account for weird user implementations of Num?
handleFunctionsZ3 d (Var "==" _ ) [_, _, a, b] = do
    a' <- exprZ3 d a
    b' <- exprZ3 d b
    mkEq a' b'
handleFunctionsZ3 d (Var ">" _ ) [_, _, a, b] = do
    a' <- exprZ3 d a
    b' <- exprZ3 d b
    mkGt a' b'
handleFunctionsZ3 d (Var "<" _ ) [_, _, a, b] = do
    a' <- exprZ3 d a
    b' <- exprZ3 d b
    mkLt a' b'
handleFunctionsZ3 d (Var ">=" _ ) [_, _, a, b] = do
    a' <- exprZ3 d a
    b' <- exprZ3 d b
    mkGe a' b'
handleFunctionsZ3 d (Var "<=" _ ) [_, _, a, b] = do
    a' <- exprZ3 d a
    b' <- exprZ3 d b
    mkLe a' b'
handleFunctionsZ3 d (Var "+" _ ) [_, _, a, b] = do
    a' <- exprZ3 d a
    b' <- exprZ3 d b
    mkAdd [a', b']
handleFunctionsZ3 d (Var "-" _ ) [_, _, a, b] = do
    a' <- exprZ3 d a
    b' <- exprZ3 d b
    mkSub [a', b']
handleFunctionsZ3 d (Var "*" _ ) [_, _, a, b] = do
    a' <- exprZ3 d a
    b' <- exprZ3 d b
    mkMul [a', b']
handleFunctionsZ3 d (Var "&&" _ ) [a, b] = do
    a' <- exprZ3 d a
    b' <- exprZ3 d b
    mkAnd [a', b']
handleFunctionsZ3 d (Var "||" _ ) [a, b] = do
    a' <- exprZ3 d a
    b' <- exprZ3 d b
    mkOr [a', b']
--Constructors for built in datatypes
handleFunctionsZ3 _ (Var "I#" _) [Const c] = constZ3 c
handleFunctionsZ3 d (Var "I#" _) [e] = exprZ3 d e
handleFunctionsZ3 _ (Var "F#" _) [Const c] = constZ3 c
handleFunctionsZ3 d (Var "F#" _) [e] = exprZ3 d e
handleFunctionsZ3 _ (Var "D#" _) [Const c] = constZ3 c
handleFunctionsZ3 d (Var "D#" _) [e] = exprZ3 d e
handleFunctionsZ3 d (Var n t1) e = do
    f <- case M.lookup n (snd d) of
                Just (c, _) -> return c
                Nothing -> mkFuncDeclZ3 d n t1
    
    e' <- mapM (exprZ3 d) e
    mkApp f e'
handleFunctionsZ3 d (Lam n e t) [e'] = do
    n' <- T.trace ("Lam " ++ n) mkStringSymbol n
    t' <- sortZ3 d . ithArgType t $ 1
    v <- mkVar n' t'
    e'' <- T.trace ("t = " ++ show t ++ " e' = " ++ show e') exprZ3 d e'
    --Possibly patterns could speed this up?
    assert =<< mkEq v e''--mkForall [] [n'] [t'] =<< exprZ3 d e
    exprZ3 d e
handleFunctionsZ3 _ e _ = error ("Unknown expression " ++ show e ++ " in handleFunctionsZ3")


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

sortFuncZ3 :: TypeMaps -> Type -> Z3 [Sort]
sortFuncZ3 d (TyFun t1 t2) = do
    t1' <- sortFuncZ3 d t1
    t2' <- sortFuncZ3 d t2
    return (t1' ++ t2')
sortFuncZ3 d t = do
    t' <- sortZ3 d t
    return [t']

sortZ3 :: TypeMaps -> Type -> Z3 Sort
sortZ3 _ TyRawInt = mkIntSort
sortZ3 _ (TyConApp "Int" _) = mkIntSort
sortZ3 _ TyRawFloat = mkRealSort
sortZ3 _ (TyConApp "Float" _) = mkRealSort
sortZ3 _ TyRawDouble = mkRealSort
sortZ3 _ (TyConApp "Double" _) = mkRealSort
sortZ3 _ (TyConApp "Bool" _) = mkBoolSort
sortZ3 (d, _) t@(TyConApp n _) =
    let
        r = M.lookup n $ d
    in
    case r of (Just r') -> return r'
              Nothing -> error ("Unknown sort in sortZ3 " ++ show t)
sortZ3 _ t = error ("Unknown sort in sortZ3 " ++ show t)


constZ3 :: Const -> Z3 AST
constZ3 (CInt i) = mkInt i =<< mkIntSort
constZ3 (CFloat r) = mkReal (fromInteger . numerator $ r) (fromInteger . denominator $ r)
constZ3 (CDouble r) = mkReal (fromInteger . numerator $ r) (fromInteger . denominator $ r)


altZ3 :: TypeMaps -> Alt -> Z3 AST
altZ3 _ (Alt (DC ("True", _, TyConApp "Bool" _, _), _)) = mkBool True
altZ3 _ (Alt (DC ("False", _, TyConApp "Bool" _, _), _)) = mkBool False
altZ3 _ (Alt (DC ("I#", _, TyConApp "Int" _, _), i)) = do
    intSort <- mkIntSort
    case i of
        [i'] -> do
            s <- mkStringSymbol i'
            mkVar s intSort
        otherwise -> mkFreshConst "intCase" intSort
    
altZ3 (d, c) (Alt (DC (x, _, TyConApp n _, ts), ns)) = do
    let sort = case M.lookup n d of
                    Just s -> s
                    Nothing -> error ("Type " ++ x ++ " not recognized.")
    cons <- getDatatypeSortConstructors sort

    rel_cons <- filterM (getRelevantCon x) cons
    let rel_con = rel_cons !! 0

    ex <- mapM (exprZ3 (d, c)) . map (\(n', t') -> Var n' t') . zip ns $ ts

    mkApp rel_con ex
    where
        getRelevantCon :: Name -> FuncDecl -> Z3 Bool
        getRelevantCon n f = do
            n' <- mkStringSymbol n
            f' <- getDeclName f
            return (n' == f')
altZ3 _ e = error ("Case of " ++ show e ++ " not handled in altZ3.")