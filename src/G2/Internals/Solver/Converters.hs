{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Converters
-- This contains functions to switch from
-- (1) A State/Exprs/Types to SMTHeaders/SMTASTs/Sorts
-- (2) SMTHeaders/SMTASTs/Sorts to some SMT solver interface
-- (3) SMTASTs/Sorts to Exprs/Types
module G2.Internals.Solver.Converters
    ( toSMTHeaders
    , toSMTHeadersWithSMTSorts
    , toSolver
    , exprToSMT --WOULD BE NICE NOT TO EXPORT THIS
    , typeToSMT --WOULD BE NICE NOT TO EXPORT THIS
    , toSolverAST --WOULD BE NICE NOT TO EXPORT THIS
    , pcVars
    , smtastToExpr
    , modelAsExpr ) where

import Control.Monad
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import qualified Data.Text as T

-- import G2.Internals.Translation.HaskellPrelude
import G2.Internals.Language.Naming
import qualified G2.Internals.Language.PathConds as PC
import G2.Internals.Language.Typing
import G2.Internals.Language.Support hiding (Model)
import G2.Internals.Language.Syntax hiding (Assert)
import G2.Internals.Solver.Language

-- | toSMTHeaders
-- Here we convert from a State, to an SMTHeader.  This SMTHeader can later
-- be given to an SMT solver by using toSolver.
-- To determine the input that can be fed to a state to get the curr_expr,
-- we need only consider the types and path constraints of that state.
-- We can also pass in some other Expr Container to instantiate names from, which is
-- important if you wish to later be able to scrape variables from those Expr's
toSMTHeaders :: State h t -> [SMTHeader]
toSMTHeaders = addSetLogic . toSMTHeaders'

toSMTHeaders' :: State h t -> [SMTHeader]
toSMTHeaders' s  = 
    let
        pc = PC.toList $ path_conds s
    in
    nub (pcVarDecls pc)
    ++
    (pathConsToSMTHeaders pc)

toSMTHeadersWithSMTSorts :: State h t -> [SMTHeader]
toSMTHeadersWithSMTSorts = addSetLogic . toSMTHeadersWithSMTSorts'

toSMTHeadersWithSMTSorts' :: State h t -> [SMTHeader]
toSMTHeadersWithSMTSorts' s =
    (typesToSMTSorts $ type_env s)
    ++
    toSMTHeaders' s

-- | addSetLogic
-- Determines an appropriate SetLogic command, and adds it to the headers
addSetLogic :: [SMTHeader] -> [SMTHeader]
addSetLogic xs =
    let
        lia = isLIA xs
        lra = isLRA xs
        lira = isLIRA xs
        nia = isNIA xs
        nra = isNRA xs
        nira = isNIRA xs

        sl = if any isSortDecl xs then SetLogic ALL else
             if lia then SetLogic QF_LIA else
             if lra then SetLogic QF_LRA else
             if lira then SetLogic QF_LIRA else
             if nia then SetLogic QF_NIA else
             if nra then SetLogic QF_NRA else 
             if nira then SetLogic QF_NIRA else SetLogic ALL
    in
    sl:xs

isSortDecl :: SMTHeader -> Bool
isSortDecl (SortDecl _) = True
isSortDecl _ = False

isNIA :: (ASTContainer m SMTAST) => m -> Bool
isNIA = getAll . evalASTs isNIA'

isNIA' :: SMTAST -> All
isNIA' (_ :* _) = All True
isNIA' (_ :/ _) = All True
isNIA' s = isLIA' s

isLIA :: (ASTContainer m SMTAST) => m -> Bool
isLIA = getAll . evalASTs isLIA'

isLIA' :: SMTAST -> All
isLIA' (_ :>= _) = All True
isLIA' (_ :> _) = All True
isLIA' (_ := _) = All True
isLIA' (_ :/= _) = All True
isLIA' (_ :< _) = All True
isLIA' (_ :<= _) = All True
isLIA' (_ :+ _) = All True
isLIA' (_ :- _) = All True
isLIA' (x :* y) = All $ isIntegerCoeff x || isIntegerCoeff y
isLIA' (Neg _) = All True
isLIA' (VInt _) = All True
isLIA' (V _ s) = All $ isIASort s
isLIA' s = isCore' s

isIASort :: Sort -> Bool
isIASort SortInt = True
isIASort s = isCoreSort s

isIntegerCoeff :: SMTAST -> Bool
isIntegerCoeff (Neg s) = isIntegerCoeff s
isIntegerCoeff (VInt _) = True
isIntegerCoeff _ = False

isNRA :: (ASTContainer m SMTAST) => m -> Bool
isNRA = getAll . evalASTs isNRA'

isNRA' :: SMTAST -> All
isNRA' (_ :* _) = All True
isNRA' (_ :/ _) = All True
isNRA' s = isLRA' s

isLRA :: (ASTContainer m SMTAST) => m -> Bool
isLRA = getAll . evalASTs isLRA'

isLRA' :: SMTAST -> All
isLRA' (_ :>= _) = All True
isLRA' (_ :> _) = All True
isLRA' (_ := _) = All True
isLRA' (_ :/= _) = All True
isLRA' (_ :< _) = All True
isLRA' (_ :<= _) = All True
isLRA' (_ :+ _) = All True
isLRA' (_ :- _) = All True
isLRA' (x :* y) = All $ isRationalCoeff x || isRationalCoeff y
isLRA' (Neg _) = All True
isLRA' (VFloat _) = All True
isLRA' (VDouble _) = All True
isLRA' (V _ s) = All $ isRASort s
isLRA' s = isCore' s

isRASort :: Sort -> Bool
isRASort SortFloat = True
isRASort SortDouble = True
isRASort s = isCoreSort s

isRationalCoeff :: SMTAST -> Bool
isRationalCoeff (Neg s) = isRationalCoeff s
isRationalCoeff (VFloat _) = True
isRationalCoeff (VDouble _) = True
isRationalCoeff _ = False

isLIRA :: (ASTContainer m SMTAST) => m -> Bool
isLIRA = getAll . evalASTs isLIRA'

isLIRA' :: SMTAST -> All
isLIRA' (ItoR _) = All True
isLIRA' s = All $ getAll (isLIA' s) || getAll (isLRA' s)

isNIRA :: (ASTContainer m SMTAST) => m -> Bool
isNIRA = getAll . evalASTs isNIRA'

isNIRA' :: SMTAST -> All
isNIRA' (ItoR _) = All True
isNIRA' s = All $ getAll (isNIA' s) || getAll (isNRA' s)

isCore :: (ASTContainer m SMTAST) => m -> Bool
isCore = getAll . evalASTs isCore'

isCore' :: SMTAST -> All
isCore' (_ := _) = All True
isCore' (_ :&& _) = All True
isCore' (_ :|| _) = All True
isCore' ((:!) _) = All True
isCore' (_ :=> _) = All True
isCore' (_ :<=> _) = All True
isCore' (VBool _) = All True
isCore' (V _ s) = All $ isCoreSort s
isCore' s = All False

isCoreSort :: Sort -> Bool
isCoreSort SortBool = True
isCoreSort _ = False

-------------------------------------------------------------------------------

-- | pathConsToSMTHeaders
pathConsToSMTHeaders :: [PathCond] -> [SMTHeader]
pathConsToSMTHeaders = map Assert . mapMaybe pathConsToSMT

pathConsToSMT :: PathCond -> Maybe SMTAST
pathConsToSMT (AltCond a e b) =
    let
        exprSMT = exprToSMT e
        altSMT = altToSMT a e
    in
    Just $ if b then exprSMT := altSMT else (:!) (exprSMT := altSMT) 
pathConsToSMT (ExtCond e b) =
    let
        exprSMT = exprToSMT e
    in
    Just $ if b then exprSMT else (:!) exprSMT
pathConsToSMT (ConsCond (DataCon (Name "True" _ _) _ _) e b) =
    let
        exprSMT = exprToSMT e
    in
    Just $ if b then exprSMT else (:!) exprSMT
pathConsToSMT (ConsCond (DataCon (Name "False" _ _) _ _) e b) =
    let
        exprSMT = exprToSMT e
    in
    Just $ if b then  (:!) $ exprSMT else exprSMT
pathConsToSMT (ConsCond (DataCon n _ _) e b) =
    let
        exprSMT = exprToSMT e
    in
    Just $ if b then Tester n exprSMT else (:!) $ Tester n exprSMT
pathConsToSMT (PCExists _) = Nothing

exprToSMT :: Expr -> SMTAST
exprToSMT (Var (Id n t)) = V (nameToStr n) (typeToSMT t)
exprToSMT (Lit c) =
    case c of
        LitInt i -> VInt i
        LitFloat f -> VFloat f
        LitDouble d -> VDouble d
        err -> error $ "exprToSMT: invalid Expr: " ++ show err
exprToSMT (Data (DataCon (Name n _ _) (TyConApp (Name "Bool" _ _) _) _)) =
    case n of
        "True" -> VBool True
        "False" -> VBool False
        _ -> error "Invalid bool in exprToSMT"
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
        getFunc p@(Prim _ _) = p
        getFunc (App a' _) = getFunc a'
        getFunc d@(Data _) = d 
        getFunc err = error $ "getFunc: invalid Expr: " ++ show err

        getArgs :: Expr -> [Expr]
        getArgs (App a1 a2) = getArgs a1 ++ [a2]
        getArgs _ = []
exprToSMT e = error $ "exprToSMT: unhandled Expr: " ++ show e

-- | funcToSMT
-- We split based on whether the passed Expr is a function or known data constructor, or an unknown data constructor
funcToSMT :: Expr -> [Expr] -> SMTAST
funcToSMT (Var (Id n t)) es = Cons (nameToStr n) (map exprToSMT es) (typeToSMT t) -- TODO : DO WE NEED THIS???
funcToSMT (Prim p _) [a] = funcToSMT1Prim p a
funcToSMT (Prim p _) [a1, a2] = funcToSMT2Prim p a1 a2
funcToSMT (Data (DataCon n t _)) es = Cons (nameToStr n) (map exprToSMT es) (typeToSMT t)
funcToSMT e l = error ("Unrecognized " ++ show e ++ " with args " ++ show l ++ " in funcToSMT")

funcToSMT1Prim :: Primitive -> Expr -> SMTAST
funcToSMT1Prim Negate a = Neg (exprToSMT a)
funcToSMT1Prim Not e = (:!) (exprToSMT e)
funcToSMT1Prim IntToFloat e = ItoR (exprToSMT e)
funcToSMT1Prim IntToDouble e = ItoR (exprToSMT e)
funcToSMT1Prim err _ = error $ "funcToSMT1Prim: invalid Primitive " ++ show err

funcToSMT2Prim :: Primitive -> Expr -> Expr -> SMTAST
funcToSMT2Prim And a1 a2 = exprToSMT a1 :&& exprToSMT a2
funcToSMT2Prim Or a1 a2 = exprToSMT a1 :|| exprToSMT a2
funcToSMT2Prim Implies a1 a2 = exprToSMT a1 :=> exprToSMT a2
funcToSMT2Prim Iff a1 a2 = exprToSMT a1 :<=> exprToSMT a2
funcToSMT2Prim Ge a1 a2 = exprToSMT a1 :>= exprToSMT a2
funcToSMT2Prim Gt a1 a2 = exprToSMT a1 :> exprToSMT a2
funcToSMT2Prim Eq a1 a2 = exprToSMT a1 := exprToSMT a2
funcToSMT2Prim Neq a1 a2 = exprToSMT a1 :/= exprToSMT a2
funcToSMT2Prim Lt a1 a2 = exprToSMT a1 :< exprToSMT a2
funcToSMT2Prim Le a1 a2 = exprToSMT a1 :<= exprToSMT a2
funcToSMT2Prim Plus a1 a2 = exprToSMT a1 :+ exprToSMT a2
funcToSMT2Prim Minus a1 a2 = exprToSMT a1 :- exprToSMT a2
funcToSMT2Prim Mult a1 a2 = exprToSMT a1 :* exprToSMT a2
funcToSMT2Prim Div a1 a2 = exprToSMT a1 :/ exprToSMT a2
funcToSMT2Prim Quot a1 a2 = exprToSMT a1 `QuotSMT` exprToSMT a2
funcToSMT2Prim Mod a1 a2 = exprToSMT a1 `Modulo` exprToSMT a2
funcToSMT2Prim op lhs rhs = error $ "funcToSMT2Prim: invalid case with (op, lhs, rhs): " ++ show (op, lhs, rhs)

altToSMT :: AltMatch -> Expr -> SMTAST
altToSMT (LitAlt (LitInt i)) _ = VInt i
altToSMT (LitAlt (LitFloat f)) _ = VFloat f
altToSMT (LitAlt (LitDouble d)) _ = VDouble d
altToSMT (DataAlt (DataCon (Name "True" _ _) _ _) _) _ = VBool True
altToSMT (DataAlt (DataCon (Name "False" _ _) _ _) _) _ = VBool False
altToSMT (DataAlt (DataCon n t ts) ns) e =
    let
        c = Cons (nameToStr n) (map f $ zip ns ts) (typeToSMT t)

        ta = typeArgs e
        t' = case (null ta, returnType t) of
            (False, TyConApp n _) -> Just $ TyConApp n ta
            _ -> Nothing
    in
    case t' of
        Just tas -> As c $ typeToSMT tas
        _ -> c
    where
        f :: (Id, Type) -> SMTAST
        f (n', t') = V (nameToStr . idName $ n') (typeToSMT t')
altToSMT am _ = error $ "Unhandled " ++ show am

typeArgs :: Expr -> [Type]
typeArgs e =
    case typeOf e of
        TyConApp _ ts -> ts
        _ -> []

createVarDecls :: [(Name, Sort)] -> [SMTHeader]
createVarDecls [] = []
createVarDecls ((n,s):xs) = VarDecl (nameToStr n) s:createVarDecls xs

pcVarDecls :: [PathCond] -> [SMTHeader]
pcVarDecls = createVarDecls . pcVars

pcVars :: [PathCond] -> [(Name, Sort)]
pcVars [] = []
pcVars (PCExists i:xs) = idToNameSort i : pcVars xs
pcVars (AltCond am e _:xs) = amVars am ++ vars e ++ pcVars xs
pcVars (p:xs)= vars p ++ pcVars xs

amVars :: AltMatch -> [(Name, Sort)]
amVars (DataAlt _ i) = map idToNameSort i
amVars _ = []

vars :: (ASTContainer m Expr) => m -> [(Name, Sort)]
vars = evalASTs vars'
    where
        vars' :: Expr -> [(Name, Sort)]
        vars' (Var i) = [idToNameSort i]
        vars' _ = []

idToNameSort :: Id -> (Name, Sort)
idToNameSort (Id n t) = (n, typeToSMT t)

typeToSMT :: Type -> Sort
typeToSMT (TyVar (Id n _)) = Sort (nameToStr n) []
typeToSMT (TyFun TyLitInt _) = SortInt -- TODO: Remove this
typeToSMT (TyFun TyLitDouble _) = SortDouble -- TODO: Remove this
typeToSMT (TyFun TyLitFloat _) = SortFloat -- TODO: Remove this
typeToSMT TyLitInt = SortInt
typeToSMT TyLitDouble = SortDouble
typeToSMT TyLitFloat = SortFloat
-- typeToSMT (TyConApp (Name "Int" _ _) _) = SortInt
-- typeToSMT (TyConApp (Name "Float" _ _) _) = SortFloat
-- typeToSMT (TyConApp (Name "Double" _ _) _) = SortDouble
typeToSMT (TyConApp (Name "Bool" _ _) _) = SortBool
typeToSMT (TyConApp n ts) = Sort (nameToStr n) (map typeToSMT ts)
typeToSMT (TyForAll (AnonTyBndr _) t) = typeToSMT t
typeToSMT (TyForAll (NamedTyBndr _) t) = Sort "TyForAll" []
typeToSMT t = error $ "Unsupported type in typeToSMT: " ++ show t

typesToSMTSorts :: TypeEnv -> [SMTHeader]
typesToSMTSorts tenv =
    [SortDecl . map typeToSortDecl $ M.toList tenv]
        where
            typeToSortDecl :: (Name, AlgDataTy) -> (SMTName, [SMTName], [DC])
            typeToSortDecl (n, DataTyCon ns dcs) = (nameToStr n, map nameToStr ns, map dataConToDC dcs)

            dataConToDC :: DataCon -> DC
            dataConToDC (DataCon n _ ts) =
                DC (nameToStr n) $ map typeToSMT ts

-- | toSolver
toSolver :: SMTConverter ast out io -> [SMTHeader] -> out
toSolver con [] = empty con
toSolver con (Assert ast:xs) = 
    merge con (assert con $ toSolverAST con ast) (toSolver con xs)
toSolver con (VarDecl n s:xs) = merge con (toSolverVarDecl con n s) (toSolver con xs)
toSolver con (SortDecl ns:xs) = merge con (toSolverSortDecl con ns) (toSolver con xs)
toSolver con (SetLogic lgc:xs) = merge con (toSolverSetLogic con lgc) (toSolver con xs)

-- | toSolverAST
toSolverAST :: SMTConverter ast out io -> SMTAST -> ast
toSolverAST con (x :>= y) = (.>=) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :> y) = (.>) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x := y) = (.=) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :/= y) = (./=) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :< y) = (.<) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :<= y) = (.<=) con (toSolverAST con x) (toSolverAST con y)

toSolverAST con (x :&& y) = (.&&) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :|| y) =  (.||) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con ((:!) x) = (.!) con $ toSolverAST con x
toSolverAST con (x :=> y) = (.=>) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :<=> y) = (.<=>) con (toSolverAST con x) (toSolverAST con y)

toSolverAST con (x :+ y) = (.+) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :- y) = (.-) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :* y) = (.*) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :/ y) = (./) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x `QuotSMT` y) = smtQuot con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x `Modulo` y) = smtModulo con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (Neg x) = neg con $ toSolverAST con x
toSolverAST con (ItoR x) = itor con $ toSolverAST con x

toSolverAST con (Tester n e) = tester con (nameToStr n) (toSolverAST con e)

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
toSolverAST con (As ast s) =
    let
        ast' = toSolverAST con ast
    in
    asSort con ast' s 
toSolverAST con (V n s) = varName con n s
toSolverAST _ ast = error $ "toSolverAST: invalid SMTAST: " ++ show ast

-- | toSolverSortDecl
toSolverSortDecl :: SMTConverter ast out io -> [(SMTName, [SMTName],  [DC])] -> out
toSolverSortDecl = sortDecl

-- | toSolverVarDecl
toSolverVarDecl :: SMTConverter ast out io -> SMTName -> Sort -> out
toSolverVarDecl con n s = varDecl con n (sortName con s)

-- | toSolverSetLogic
toSolverSetLogic :: SMTConverter ast out io -> Logic -> out
toSolverSetLogic = setLogic

-- | smtastToExpr
smtastToExpr :: SMTAST -> Expr
smtastToExpr (VInt i) = (Lit $ LitInt i)
smtastToExpr (VFloat f) = (Lit $ LitFloat f)
smtastToExpr (VDouble d) = (Lit $ LitDouble d)
smtastToExpr (VBool b) =
    Data (DataCon (Name (T.pack $ show b) Nothing 0) (TyConApp (Name "Bool" Nothing 0) []) [])
smtastToExpr (Cons n smts s) =
    foldl (\v a -> App v (smtastToExpr a)) (Data (DataCon (strToName n) (sortToType s) [])) smts
smtastToExpr (V n s) = Var $ Id (strToName n) (sortToType s)
smtastToExpr _ = error "Conversion of this SMTAST to an Expr not supported."

sortToType :: Sort -> Type
sortToType (SortInt) = TyLitInt
sortToType (SortFloat) = TyLitFloat
sortToType (SortDouble) = TyLitDouble
sortToType (SortBool) = TyConApp (Name "Bool" Nothing 0) []
sortToType (Sort n xs) = TyConApp (strToName n) (map sortToType xs)

modelAsExpr :: Model -> ExprModel
modelAsExpr = M.mapKeys strToName . M.map smtastToExpr
