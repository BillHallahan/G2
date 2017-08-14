-- | Converters
-- This contains functions to switch from
-- (1) A State/Exprs/Types to SMTHeaders/SMTASTs/Sorts
-- (2) SMTHeaders/SMTASTs/Sorts to some SMT solver interface
-- (3) SMTASTs/Sorts to Exprs/Types
module G2.Internals.SMT.Converters
    ( toSMTHeaders
    , toSolver
    , sltToSMTNameSorts
    , exprToSMT --WOULD BE NICE NOT TO EXPORT THIS
    , typeToSMT --WOULD BE NICE NOT TO EXPORT THIS
    , toSolverAST --WOULD BE NICE NOT TO EXPORT THIS
    {- , smtastToExpr
    , sortToType
    , modelAsExpr -} ) where

import qualified Data.Map as M

-- import G2.Internals.Translation.HaskellPrelude
import G2.Internals.Language.Naming
import G2.Internals.Language.Support
import qualified G2.Internals.Language.SymLinks as SLT
import G2.Internals.Language.Syntax hiding (Assert)
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
    (map pathConsToSMT $ path_conds s)

pathConsToSMT :: PathCond -> SMTHeader
pathConsToSMT (AltCond e a b) =
    let
        exprSMT = exprToSMT e
        altSMT = altToSMT a
    in
    Assert $ if b then exprSMT := altSMT else (:!) (exprSMT := altSMT) 
pathConsToSMT (ExtCond e b) =
    let
        exprSMT = exprToSMT e
    in
    Assert $ if b then exprSMT else (:!) exprSMT

exprToSMT :: Expr -> SMTAST
exprToSMT (Var (Id n t)) = V (nameToStr n) (typeToSMT t)
exprToSMT (Lit c) =
    case c of
        LitInt i -> VInt i
        LitFloat f -> VFloat f
        LitDouble d -> VDouble d
exprToSMT (Data (DataCon n t _)) = V (nameToStr n) (typeToSMT t)
exprToSMT a@(App _ _) =
    let
        f = getFunc a
        args = getArgs a
    in
    funcToSMT f args
    where
        getFunc :: Expr -> Expr
        getFunc v@(Var _) = v
        getFunc p@(Prim _) = p
        getFunc (App a' _) = getFunc a'
        getFunc d@(Data _) = d 

        getArgs :: Expr -> [Expr]
        getArgs (App a1 a2) = getArgs a1 ++ [a2]
        getArgs _ = []
exprToSMT e = error ("Unhandled expression " ++ show e)

-- | funcToSMT
-- We split based on whether the passed Expr is a function or known data constructor, or an unknown data constructor
funcToSMT :: Expr -> [Expr] -> SMTAST
funcToSMT (Var (Id n t)) es = Cons (nameToStr n) (map exprToSMT es) (typeToSMT t)
funcToSMT (Prim p) [a] = funcToSMT1Prim p a
funcToSMT (Prim p) [a1, a2] = funcToSMT2Prim p a1 a2
funcToSMT (Data (DataCon n t _)) es = Cons (nameToStr n) (map exprToSMT es) (typeToSMT t)
funcToSMT e@(Data _) [a] = funcToSMT1Var e a
funcToSMT e _ = error ("Unrecognized " ++ show e ++ " in funcToSMT")

funcToSMT1Var :: Expr -> Expr -> SMTAST
funcToSMT1Var f a
    | f == Prim (UNeg) = Neg (exprToSMT a)
    | f == Data (PrimCon I) = exprToSMT a
    | f == Data (PrimCon F) = exprToSMT a
    | f == Data (PrimCon D) = exprToSMT a
    | otherwise = error ("Unhandled function " ++ show f ++ " in funcToSMT1.")

funcToSMT1Prim :: Primitive -> Expr -> SMTAST
funcToSMT1Prim Not e = (:!) (exprToSMT e)

funcToSMT2Prim :: Primitive -> Expr -> Expr -> SMTAST
funcToSMT2Prim And a1 a2 = exprToSMT a1 :&& exprToSMT a2
funcToSMT2Prim Or a1 a2 = exprToSMT a1 :|| exprToSMT a2
funcToSMT2Prim Ge a1 a2 = exprToSMT a1 :>= exprToSMT a2
funcToSMT2Prim Gt a1 a2 = exprToSMT a1 :> exprToSMT a2
funcToSMT2Prim Eq a1 a2 = exprToSMT a1 := exprToSMT a2
funcToSMT2Prim Lt a1 a2 = exprToSMT a1 :< exprToSMT a2
funcToSMT2Prim Le a1 a2 = exprToSMT a1 :<= exprToSMT a2
funcToSMT2Prim Implies a1 a2 = exprToSMT a1 :=> exprToSMT a2
funcToSMT2Prim Plus a1 a2 = exprToSMT a1 :+ exprToSMT a2
funcToSMT2Prim Minus a1 a2 = exprToSMT a1 :- exprToSMT a2
funcToSMT2Prim Mult a1 a2 = exprToSMT a1 :* exprToSMT a2
funcToSMT2Prim Div a1 a2 = exprToSMT a1 :/ exprToSMT a2

altToSMT :: AltMatch -> SMTAST
altToSMT (LitAlt (LitInt i)) = VInt i
altToSMT (LitAlt (LitFloat f)) = VFloat f
altToSMT (LitAlt (LitDouble d)) = VDouble d
altToSMT (LitAlt (LitBool b)) = VBool b
altToSMT (DataAlt (PrimCon I) [i]) = V (nameToStr . idName $ i) SortInt
altToSMT (DataAlt (PrimCon D) [d]) = V (nameToStr . idName $ d) SortDouble
altToSMT (DataAlt (PrimCon F) [f]) = V (nameToStr . idName $ f) SortFloat
altToSMT (DataAlt (DataCon n t@(TyConApp _ _) ts) ns) =
    Cons (nameToStr n) (map f $ zip ns ts) (typeToSMT t)
    where
        f :: (Id, Type) -> SMTAST
        f (n', t') = V (nameToStr . idName $ n') (typeToSMT t')

sltToSMTNameSorts :: SymLinks -> [(Name, Sort)]
sltToSMTNameSorts = map (\(n, t) -> (n, typeToSMT t)) . SLT.namesTypes

typeToSMT :: Type -> Sort
typeToSMT TyInt = SortInt
typeToSMT TyDouble = SortDouble
typeToSMT TyFloat = SortFloat
typeToSMT TyBool = SortBool
typeToSMT (TyConApp n _) = Sort (nameToStr n) []
typeToSMT _ = Sort "" []

typesToSMTSorts :: TypeEnv -> [SMTHeader]
typesToSMTSorts tenv =
    [SortDecl . map typeToSortDecl $ M.toList tenv]
        where
            typeToSortDecl :: (Name, AlgDataTy) -> (SMTName, [DC])
            typeToSortDecl (n, AlgDataTy _ dcs) = (nameToStr n, map dataConToDC dcs)

            dataConToDC :: DataCon -> DC
            dataConToDC (DataCon n _ ts) =
                DC (nameToStr n) $ map typeToSMT ts

createVarDecls :: [(Name, Sort)] -> [SMTHeader]
createVarDecls [] = []
createVarDecls ((n,s):xs) = VarDecl (nameToStr n) s:createVarDecls xs

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
toSolverSortDecl :: SMTConverter ast out io -> [(SMTName, [DC])] -> out
toSolverSortDecl = sortDecl

-- | toSolverVarDecl
toSolverVarDecl :: SMTConverter ast out io -> SMTName -> Sort -> out
toSolverVarDecl con n s = varDecl con n (sortName con s)

-- | smtastToExpr
{- TODO:
smtastToExpr :: SMTAST -> Expr
smtastToExpr (VInt i) = Lit $ LitInt i
smtastToExpr (VFloat f) = Lit $ LitFloat f
smtastToExpr (VDouble d) = Lit $ LitDouble d
smtastToExpr (VBool b) = Lit $ LitBool b
smtastToExpr (Cons n smts s) = foldl (\v a -> App v (smtastToExpr a)) (Data (DataCon n 0 (sortToType s) [])) smts
smtastToExpr (V n s) = Var $ Id n (sortToType s)

sortToType :: Sort -> Type
sortToType (SortInt) = TyConApp "Int" []
sortToType (SortFloat) = TyConApp "Float" []
sortToType (SortDouble) = TyConApp "Double" []
sortToType (SortBool) = TyConApp "Bool" []
sortToType (Sort n xs) = TyConApp n (map sortToType xs)

modelAsExpr :: Model -> ExprModel
modelAsExpr = M.map smtastToExpr
-}
