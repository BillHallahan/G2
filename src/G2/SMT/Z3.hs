module G2.SMT.Z3 where

import G2.Core.Language
import G2.Core.Evaluator
import G2.Core.Utils
import G2.Haskell.Prelude

import Control.Monad

import Data.List
import qualified Data.Map  as M
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
reachabilitySolverZ3 (tv, ev, expr, pc) = do
    dtMap <- mkDatatypesZ3 tv
    
    mapM assert =<< constraintsZ3 dtMap pc
    solverCheckAndGetModel 

--Use the SMT solver to attempt to find inputs that will result in output
--satisfying the given curr expr
outputSolverZ3 :: State -> Z3 (Result, Maybe Model)
outputSolverZ3 (tv, ev, expr, pc)  = do
    dtMap <- mkDatatypesZ3 tv

    assert =<< exprZ3 dtMap expr
    mapM assert =<< constraintsZ3 dtMap pc

    solverCheckAndGetModel

constraintsZ3 :: M.Map Name Sort -> PC -> Z3 [AST]
constraintsZ3 d (pc) = do
    mapM (constraintsZ3' d) pc
    where
        constraintsZ3' :: M.Map Name Sort -> (Expr, Alt, Bool) -> Z3 AST
        constraintsZ3' d (expr, alt, b) = do
            e <- exprZ3 d expr
            a <- altZ3 d alt

            if b then mkEq e a else mkNot =<< mkEq e a

mkDatatypesZ3 :: TEnv -> Z3 (M.Map Name Sort)
mkDatatypesZ3 tenv = mkSortsZ3 M.empty
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

        mkSortsZ3 :: M.Map Name Sort -> [(Name, Type)] -> Z3 (M.Map Name Sort)
        mkSortsZ3 d ((n, t@(TyAlg n' dcs)):xs) = do
            let r = requires t

            let (s, s') = partition (\(n'', _) -> n'' `elem` r) xs
            d' <- mkSortsZ3 d s

            cons <- mapM (mkConstructorZ3 d') dcs
            nSymb <- mkStringSymbol n
            da <- mkDatatype nSymb cons
            mkSortsZ3 (M.insert n da d') s'
        mkSortsZ3 d [] = return d

mkConstructorZ3 :: M.Map Name Sort -> DataCon -> Z3 Constructor
--we need to do something to ensure all symbols are unique... adjust
mkConstructorZ3 d (DC (n, _, tc, t)) = do
    n' <- mkStringSymbol n
    is_n <- mkStringSymbol ("is_" ++ n)
    s <- mapM mkStringSymbol . numFresh n (length t) $ []
    t' <- mapM (\_t -> if _t /= tc then return .  Just =<< sortZ3 d _t else return  Nothing) t

    mkConstructor n' is_n . map (\(s, t) -> (s, t, 0)) . zip s $ t'

exprZ3 :: M.Map Name Sort -> Expr -> Z3 AST
exprZ3 _ (Var "True" _) = mkTrue
exprZ3 _ (Var "False" _) = mkFalse
exprZ3 d (Var v t) = do
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
    r <- mkFreshConst "case" =<< sortZ3 d t

    assert =<< mkAnd =<< mapM (exprZ3AltExpr d e' r) ae
    return r
    where
        {- M.Map Name Sort
            -> the expression being evaluated
            -> the expression to store result
            -> alt, expr pairs
            -> the implies
        -}
        exprZ3AltExpr :: M.Map Name Sort -> AST -> AST -> (Alt, Expr) -> Z3 AST
        exprZ3AltExpr d eq eq' (_a, _e) = do
            _a' <- altZ3 d _a
            _a_eq <- mkEq _a' eq

            _e' <- exprZ3 d _e
            _e_eq <- mkEq _e' eq'

            mkImplies _a_eq _e_eq
exprZ3 d e = error ("Unknown expression " ++ show e ++ " in exprZ3")

handleFunctionsZ3 :: M.Map Name Sort -> Expr -> [Expr] -> Z3 AST
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
    n' <- mkStringSymbol n

    sorts <- sortFuncZ3 d t1
    let (sorts', sort'') = frontLast sorts

    f <- mkFuncDecl n' sorts' sort''
    
    e' <- mapM (exprZ3 d) e
    mkApp f e'
    where
        frontLast :: [a] -> ([a], a)
        frontLast (x:[]) = ([], x)
        frontLast (x:xs) =
            let
                (fl, fl') = frontLast xs
            in
            (x:fl, fl')
        frontLast [] = error "Empty list passed to frontLast in handleFunctionsZ3."
handleFunctionsZ3 _ e _ = error ("Unknown expression " ++ show e ++ " in handleFunctionsZ3")

sortFuncZ3 :: M.Map Name Sort -> Type -> Z3 [Sort]
sortFuncZ3 d (TyFun t1 t2) = do
    t1' <- sortFuncZ3 d t1
    t2' <- sortFuncZ3 d t2
    return (t1' ++ t2')
sortFuncZ3 d t = do
    t' <- sortZ3 d t
    return [t']

sortZ3 :: M.Map Name Sort -> Type -> Z3 Sort
sortZ3 _ TyRawInt = mkIntSort
sortZ3 _ (TyConApp "Int" _) = mkIntSort
sortZ3 _ TyRawFloat = mkRealSort
sortZ3 _ (TyConApp "Float" _) = mkRealSort
sortZ3 _ TyRawDouble = mkRealSort
sortZ3 _ (TyConApp "Double" _) = mkRealSort
sortZ3 _ (TyConApp "Bool" _) = mkBoolSort
sortZ3 d t@(TyConApp n _) =
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


altZ3 :: M.Map Name Sort -> Alt -> Z3 AST
altZ3 _ (Alt (DC ("True", _, TyConApp "Bool" _, _), _)) = mkBool True
altZ3 _ (Alt (DC ("False", _, TyConApp "Bool" _, _), _)) = mkBool False
altZ3 _ (Alt (DC ("I#", _, TyConApp "Int" _, _), i)) = do
    intSort <- mkIntSort
    case i of
        [i'] -> do
            s <- mkStringSymbol i'
            mkVar s intSort
        otherwise -> mkFreshConst "intCase" intSort
    
altZ3 d (Alt (DC (x, _, TyConApp n _, ts), ns)) = do
    let sort = case M.lookup n d of
                    Just s -> s
                    Nothing -> error ("Type " ++ x ++ " not recognized.")
    cons <- getDatatypeSortConstructors sort

    rel_cons <- filterM (getRelevantCon x) cons
    let rel_con = rel_cons !! 0

    ex <- mapM (exprZ3 d) . map (\(n', t') -> Var n' t') . zip ns $ ts

    mkApp rel_con ex
    where
        getRelevantCon :: Name -> FuncDecl -> Z3 Bool
        getRelevantCon n f = do
            n' <- mkStringSymbol n
            f' <- getDeclName f
            return (n' == f')
altZ3 _ e = error ("Case of " ++ show e ++ " not handled in altZ3.")