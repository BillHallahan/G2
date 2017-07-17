-- | Converters
-- This contains functions to switch from
-- (1) A State/Exprs/Types to SMTHeaders/SMTASTs/Sorts
-- (2) SMTHeaders/SMTASTs/Sorts to some SMT solver interface
-- (3) SMTASTs/Sorts to Exprs/Types
module G2.Internals.SMT.Converters ( toSMTHeaders
                                   , toSolver
                                   , sltToSMTNameSorts
                                   , exprToSMT --WOULD BE NICE NOT TO EXPORT THIS
                                   , typeToSMT --WOULD BE NICE NOT TO EXPORT THIS
                                   , toSolverAST --WOULD BE NICE NOT TO EXPORT THIS
                                   , smtastToExpr
                                   , sortToType
                                   , modelAsExpr) where

import qualified Data.Map as M

import G2.Internals.Translation.HaskellPrelude
import G2.Internals.Core.Language hiding (Assert)
import G2.Internals.SMT.Language

-- | toSMTHeaders
-- Here we convert from a State, to an SMTHeader.  This SMTHeader can later
-- be given to an SMT solver by using toSolver.
-- To determine the input that can be fed to a state to get the curr_expr,
-- we need only consider the types and path constraints of that state.
-- Of course, we can also solve for the curr_expr, to also get the output.
toSMTHeaders :: State -> [SMTHeader]
toSMTHeaders s = 
    (typesToSMTSorts $ type_env s)
    ++
    (createVarDecls . sltToSMTNameSorts $ sym_links s)
    ++
    (map pathConsToSMT $ path_cons s)

pathConsToSMT :: PathCond -> SMTHeader
pathConsToSMT (CondAlt e a b) =
    let
        exprSMT = exprToSMT e
        altSMT = altToSMT a
    in
    Assert $ if b then exprSMT := altSMT else (:!) (exprSMT := altSMT) 
pathConsToSMT (CondExt e b) =
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
exprToSMT (Data (DataCon n _ t _)) = V n (typeToSMT t)
exprToSMT a@(App _ _) =
    let
        f = getFunc a
        args = getArgs a
    in
    funcToSMT f args
    where
        getFunc :: Expr -> Expr
        getFunc v@(Var _ _) = v
        getFunc p@(Prim _ _) = p
        getFunc (App a' _) = getFunc a'
        getFunc d@(Data _) = d 

        getArgs :: Expr -> [Expr]
        getArgs (App a1 a2) = getArgs a1 ++ [a2]
        getArgs _ = []
exprToSMT e = error ("Unhandled expression " ++ show e)

-- | funcToSMT
-- We split based on whether the passed Expr is a function or known data constructor, or an unknown data constructor
funcToSMT :: Expr -> [Expr] -> SMTAST
funcToSMT (Var n t) es = Cons n (map exprToSMT es) (typeToSMT t)
funcToSMT (Prim p _) [a] = funcToSMT1Prim p a
funcToSMT (Prim p _) [a1, a2] = funcToSMT2Prim p a1 a2
funcToSMT (Data (DataCon n _ t _)) es = Cons n (map exprToSMT es) (typeToSMT t)
funcToSMT e@(Data _) [a] = funcToSMT1Var e a
funcToSMT e _ = error ("Unrecognized " ++ show e ++ " in funcToSMT")

funcToSMT1Var :: Expr -> Expr -> SMTAST
funcToSMT1Var f a
    | isVarName f "-" = Neg (exprToSMT a)
    | f == Data (PrimCon I) = exprToSMT a
    | f == Data (PrimCon F) = exprToSMT a
    | f == Data (PrimCon D) = exprToSMT a
    | otherwise = error ("Unhandled function " ++ show f ++ " in funcToSMT1.")

funcToSMT1Prim :: Prim -> Expr -> SMTAST
funcToSMT1Prim Not e = (:!) (exprToSMT e)

funcToSMT2Prim :: Prim -> Expr -> Expr -> SMTAST
funcToSMT2Prim And a1 a2 = exprToSMT a1 :&& exprToSMT a2
funcToSMT2Prim Or a1 a2 = exprToSMT a1 :|| exprToSMT a2
funcToSMT2Prim GE a1 a2 = exprToSMT a1 :>= exprToSMT a2
funcToSMT2Prim GrT a1 a2 = exprToSMT a1 :> exprToSMT a2
funcToSMT2Prim EQL a1 a2 = exprToSMT a1 := exprToSMT a2
funcToSMT2Prim LsT a1 a2 = exprToSMT a1 :< exprToSMT a2
funcToSMT2Prim LE a1 a2 = exprToSMT a1 :<= exprToSMT a2
funcToSMT2Prim Implies a1 a2 = exprToSMT a1 :=> exprToSMT a2
funcToSMT2Prim Plus a1 a2 = exprToSMT a1 :+ exprToSMT a2
funcToSMT2Prim Minus a1 a2 = exprToSMT a1 :- exprToSMT a2
funcToSMT2Prim Mult a1 a2 = exprToSMT a1 :* exprToSMT a2
funcToSMT2Prim Div a1 a2 = exprToSMT a1 :/ exprToSMT a2

isVarName :: Expr -> Name -> Bool
isVarName (Var n _) n' = n == n'
isVarName _ _ = False

altToSMT :: Alt -> SMTAST
altToSMT (Alt (PrimCon DTrue, _)) = VBool True
altToSMT (Alt (PrimCon DFalse, _)) = VBool False
altToSMT (Alt (PrimCon I, [i])) = V i SortInt
altToSMT (Alt (PrimCon D, [d])) = V d SortDouble
altToSMT (Alt (PrimCon F, [f])) = V f SortFloat
altToSMT (Alt (DataCon n _ t@(TyConApp _ _) ts, ns)) =
    Cons n (map f $ zip ns ts) (typeToSMT t)
    where
        f :: (Name, Type) -> SMTAST
        f (n', t') = V n' (typeToSMT t')

sltToSMTNameSorts :: SymLinkTable -> [(Name, Sort)]
sltToSMTNameSorts = map sltToSMTNameSorts' . M.toList
    where
        sltToSMTNameSorts' :: (Name, (Name, Type, Maybe Int)) -> (Name, Sort)
        sltToSMTNameSorts' (n, (_, t, _)) = (n, typeToSMT t)

typeToSMT :: Type -> Sort
typeToSMT TyInt = SortInt
typeToSMT TyDouble = SortDouble
typeToSMT TyFloat = SortFloat
typeToSMT TyBool = SortBool
typeToSMT (TyConApp n _) = Sort n []
typeToSMT _ = Sort "" []

typesToSMTSorts :: TEnv -> [SMTHeader]
typesToSMTSorts tenv =
    let
        knownTypes = map (fst . fst) prelude_t_decls
        tenv' = M.filterWithKey (\k _ -> not (k `elem` knownTypes)) tenv
    in
    [SortDecl . map typeToSortDecl $ M.elems tenv']
        where
            typeToSortDecl :: Type -> (Name, [DC])
            typeToSortDecl (TyAlg n dcs) = (n, map dataConToDC dcs)

            dataConToDC :: DataCon -> DC
            dataConToDC (DataCon n _ _ ts) =
                DC n $ map typeToSMT ts

createVarDecls :: [(Name, Sort)] -> [SMTHeader]
createVarDecls [] = []
createVarDecls ((n,s):xs) = VarDecl n s:createVarDecls xs

-- | toSolver
toSolver :: SMTConverter ast out io -> [SMTHeader] -> out
toSolver con [] = empty con
toSolver con (Assert ast:xs) = 
    merge con (assert con $ toSolverAST con ast) (toSolver con xs)
toSolver con (VarDecl n s:xs) = merge con (toSolverVarDecl con n s) (toSolver con xs)
toSolver con (SortDecl ns:xs) = merge con (toSolverSortDecl con ns) (toSolver con xs)

-- | toSolverAST
toSolverAST :: SMTConverter ast out io -> SMTAST -> ast
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
toSolverSortDecl :: SMTConverter ast out io -> [(Name, [DC])] -> out
toSolverSortDecl con = sortDecl con

-- | toSolverVarDecl
toSolverVarDecl :: SMTConverter ast out io -> Name -> Sort -> out
toSolverVarDecl con n s = varDecl con n (sortName con s)

-- | smtastToExpr
smtastToExpr :: SMTAST -> Expr
smtastToExpr (VInt i) = Const (CInt i)
smtastToExpr (VFloat f) = Const (CFloat f)
smtastToExpr (VDouble d) = Const (CDouble d)
smtastToExpr (VBool b) = Var (if b then "True" else "False") (TyConApp "Bool" [])
smtastToExpr (Cons n smts s) = foldl (\v a -> App v (smtastToExpr a)) (Data (DataCon n 0 (sortToType s) [])) smts
smtastToExpr (V n s) = Var n (sortToType s)

sortToType :: Sort -> Type
sortToType (SortInt) = TyConApp "Int" []
sortToType (SortFloat) = TyConApp "Float" []
sortToType (SortDouble) = TyConApp "Double" []
sortToType (SortBool) = TyConApp "Bool" []
sortToType (Sort n xs) = TyConApp n (map sortToType xs)

modelAsExpr :: Model -> ExprModel
modelAsExpr = M.map smtastToExpr
