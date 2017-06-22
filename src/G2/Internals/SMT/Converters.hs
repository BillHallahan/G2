module G2.Internals.SMT.Converters ( toSMTHeaders
                                   , toSolver) where

import Data.List
import qualified Data.Map as M

import G2.Internals.Translation.HaskellPrelude
import G2.Internals.Core.Language hiding (Assert)
import G2.Internals.SMT.Language
import G2.Internals.SMT.Utils

-- | toSMTHeaders
-- Here we convert from a State, to an SMTHeader.  This SMTHeader can later
-- be given to an SMT solver by using toSolver.
-- To determine the input that can be fed to a state to get the curr_expr,
-- we need only consider the types and path constraints of that state.
-- Of course, we can also solve for the curr_expr, to also get the output.
toSMTHeaders :: State -> [SMTHeader]
toSMTHeaders s = 
    let
        pcSMT = map pathConsToSMT $ path_cons s
    in
    (typesToSMTSorts $ type_env s)
    ++
    (createVarDecls . varNamesSorts $ pcSMT)
    ++
    pcSMT

pathConsToSMT :: PathCond -> SMTHeader
pathConsToSMT (CondAlt e a b) =
    let
        exprSMT = exprToSMT e
        altSMT = altToSMT a
    in
    Assert $ if b then exprSMT := altSMT else (:!) (exprSMT := altSMT) 
toSMTPathCons (CondExt e b) =
    let
        exprSMT = exprToSMT e
    in
    Assert $ if b then exprSMT else (:!) exprSMT 

exprToSMT :: Expr -> SMTAST
exprToSMT (Var n t) = V n (typeToSMT t)
exprToSMT (Const c) =
    case c of
        CInt i -> VInt i
        CFloat f -> VFloat f
        CDouble d -> VDouble d
exprToSMT a@(App _ _) =
    let
        f = getFunc a
        args = getArgs a
    in
    funcToSMT f args
    where
        getFunc :: Expr -> Expr
        getFunc v@(Var _ _) = v
        getFunc (App a _) = getFunc a

        getArgs :: Expr -> [Expr]
        getArgs (App a a') = getArgs a ++ [a']
        getArgs _ = []

funcToSMT :: Expr -> [Expr] -> SMTAST
funcToSMT e [a] = funcToSMT1 e a
funcToSMT e [a1, a2] = funcToSMT2 e (a1, a2)
funcToSMT e [a1, a2, a3, a4] = funcToSMT4 e (a1, a2, a3, a4)

funcToSMT1 :: Expr -> Expr -> SMTAST
funcToSMT1 f a
    | isVarName f "!" = (:!) (exprToSMT a)
    | isVarName f "-" = Neg (exprToSMT a)
    | isVarName f "I#" = exprToSMT a
    | isVarName f "F#" = exprToSMT a
    | isVarName f "D#" = exprToSMT a
    | otherwise = error ("Unhandled function " ++ show f ++ " in funcToSMT1.")

funcToSMT2 :: Expr -> (Expr, Expr) -> SMTAST
funcToSMT2 f (a1, a2)
    | isVarName f "&&" = exprToSMT a1 :&& exprToSMT a2
    | isVarName f "||" = exprToSMT a1 :|| exprToSMT a2
    | otherwise = error ("Unhandled function " ++ show f ++ " in funcToSMT2.")

funcToSMT4 :: Expr -> (Expr, Expr, Expr, Expr) -> SMTAST
funcToSMT4 f (a1, a2, a3, a4)
    | isVarName f ">=" && isIDF a1 = exprToSMT a3 :>= exprToSMT a4
    | isVarName f ">" && isIDF a1 = exprToSMT a3 :> exprToSMT a4
    | isVarName f "==" && isIDF a1 = exprToSMT a3 := exprToSMT a4
    | isVarName f "<" && isIDF a1 = exprToSMT a3 :< exprToSMT a4
    | isVarName f "<=" && isIDF a1 = exprToSMT a3 :<= exprToSMT a4

    | isVarName f "+" && isIDF a1 = exprToSMT a3 :+ exprToSMT a4
    | isVarName f "-" && isIDF a1 = exprToSMT a3 :- exprToSMT a4
    | isVarName f "*" && isIDF a1 = exprToSMT a3 :* exprToSMT a4
    | isVarName f "/" && isIDF a1 = exprToSMT a3 :/ exprToSMT a4
    | otherwise = error ("Unhandled function " ++ show f ++ " in funcToSMT4.")
    where
        isIDF :: Expr -> Bool
        isIDF (Type (TyConApp "Int" [])) = True
        isIDF (Type (TyConApp "Double" [])) = True
        isIDF (Type (TyConApp "Float" [])) = True
        isIDF t = False

isVarName :: Expr -> Name -> Bool
isVarName (Var n _) n' = n == n'
isVarName _ _ = False

altToSMT :: Alt -> SMTAST
altToSMT (Alt (DataCon "True" _ (TyConApp "Bool" _) _, _)) = VBool True
altToSMT (Alt (DataCon "False" _ (TyConApp "Bool" _) _, _)) = VBool False
altToSMT (Alt (DataCon "I#" _ (TyConApp "Int" _) _, [i])) = V i SortInt
altToSMT (Alt (DataCon "D#" _ (TyConApp "Double" _) _, [d])) = V d SortDouble
altToSMT (Alt (DataCon "F#" _ (TyConApp "Float" _) _, [f])) = V f SortFloat
altToSMT (Alt (DataCon n _ t@(TyConApp _ _) ts, ns)) =
    Cons n (map f $ zip ns ts) (typeToSMT t)
    where
        f :: (Name, Type) -> SMTAST
        f (n, t) = V n (typeToSMT t)

typeToSMT :: Type -> Sort
typeToSMT (TyConApp "Int" _) = SortInt
typeToSMT (TyConApp "Double" _) = SortDouble
typeToSMT (TyConApp "Float" _) = SortFloat
typeToSMT (TyConApp "Bool" _) = SortBool
typeToSMT (TyConApp n _) = Sort n []


typesToSMTSorts :: TEnv -> [SMTHeader]
typesToSMTSorts tenv =
    let
        knownTypes = map fst prelude_t_decls
        tenv' = M.filterWithKey (\k _ -> not (k `elem` knownTypes)) tenv
    in
    [SortDecl . map typeToSortDecl $ M.elems tenv']
        where
            typeToSortDecl :: Type -> (Name, [DC])
            typeToSortDecl (TyAlg n dcs) = (n, map dataConToDC dcs)

            dataConToDC :: DataCon -> DC
            dataConToDC (DataCon n _ _ ts) =
                DC n $ map (\(TyConApp t _) -> Sort t []) ts

createVarDecls :: [(Name, Sort)] -> [SMTHeader]
createVarDecls [] = []
createVarDecls ((n,s):xs) = VarDecl n s:createVarDecls xs

-- | toSolver
toSolver :: SMTConverter ast out -> [SMTHeader] -> out
toSolver con [] = empty con
toSolver con (Assert ast:xs) = 
    merge con (assert con $ toSolverAST con ast) (toSolver con xs)
toSolver con (VarDecl n s:xs) = merge con (toSolverVarDecl con n s) (toSolver con xs)
toSolver con (SortDecl ns:xs) = merge con (toSolverSortDecl con ns) (toSolver con xs)

-- | toSolverAST
toSolverAST :: SMTConverter ast out -> SMTAST -> ast
toSolverAST con (x :>= y) = (.>=) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :> y) = (.>) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x := y) = (.=) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :< y) = (.<) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :<= y) = (.<=) con (toSolverAST con x) (toSolverAST con y)

toSolverAST con (x :&& y) = (.&&) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :|| y) =  (.||) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con ((:!) x) = (.!) con $ toSolverAST con x
toSolverAST con (x :=> y) = (.=>) con (toSolverAST con x) (toSolverAST con y)

toSolverAST con (x :+ y) = (.+) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :- y) = (.-) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :* y) = (.*) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :/ y) = (./) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (Neg x) = neg con $ toSolverAST con x

toSolverAST con (Ite x y z) =
    ite con (toSolverAST con x) (toSolverAST con y) (toSolverAST con z)

toSolverAST con (VInt i) = int con i
toSolverAST con (VFloat f) = float con f
toSolverAST con (VDouble i) = double con i
toSolverAST con (VBool b) = bool con b
toSolverAST con (Cons n asts s) =
    let
        asts' = map (toSolverAST con) asts
    in
    cons con n asts' s

toSolverAST con (V n s) = varName con n s

-- | toSolverSortDecl
toSolverSortDecl :: SMTConverter ast out -> [(Name, [DC])] -> out
toSolverSortDecl con = sortDecl con

-- | toSolverVarDecl
toSolverVarDecl :: SMTConverter ast out -> Name -> Sort -> out
toSolverVarDecl con n s = varDecl con n (sortName con s)

-- | toSolverSort
toSolverSort :: SMTConverter ast out -> Sort -> ast
toSolverSort con SortInt = sortInt con
toSolverSort con SortFloat = sortFloat con
toSolverSort con SortDouble = sortDouble con
toSolverSort con SortBool = sortBool con
toSolverSort con (Sort n s) = sortADT con n s