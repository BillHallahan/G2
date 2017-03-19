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

import Debug.Trace

--This function is just kind of a hack for now... might want something else later?
printModel :: State -> IO ()
printModel s = do
    (r, m) <- evalZ3 . stateSolverZ3 $ s
    m' <- case m of Just m'' -> modelToIOString m''
                    Nothing -> return ""
    print r
    putStrLn m'

modelToIOString :: Model -> IO (String)
modelToIOString m = evalZ3 . modelToString $ m

stateSolverZ3 :: State -> Z3 (Result, Maybe Model)
stateSolverZ3 (tv, ev, expr, pc) = do
    dtMap <- mkDatatypesZ3 tv
    exprZ3 dtMap expr
    constraintsZ3 dtMap pc
    solverCheckAndGetModel 

constraintsZ3 :: M.Map Name Sort -> PC -> Z3 ()
constraintsZ3 d ((expr, alt):xs) = do
    e <- exprZ3 d expr
    a <- altZ3 d alt

    assert =<< mkEq e a

    constraintsZ3 d xs
constraintsZ3 _ ([]) = return ()

mkDatatypesZ3 :: TEnv -> Z3 (M.Map Name Sort)
mkDatatypesZ3 tenv = foldM mkSortsZ3 M.empty
                     . sortBy requires
                     . M.toList
                     . M.filterWithKey (\k _  -> not (k `S.member` knownTypes)) $ tenv
    where
        knownTypes = S.fromList . map fst $ prelude_t_decls

        requires :: (Name, Type) -> (Name, Type) -> Ordering
        requires (_, (TyAlg n1 t1)) (_, (TyAlg n2 t2)) =
            let
                t1' = catMaybes . map names . concat . map (\(DC (_, _, _, t')) -> t') $ t1
                t2' = catMaybes . map names . concat . map (\(DC (_, _, _, t')) -> t') $ t2
            in
            if n1 `elem` t2' then LT
                else if n2 `elem` t1' then GT
                    else n1 `compare` n2
        requires _ _ = error "Must only pass TyAlg's to requires in mkDatatypesZ3"

        names :: Type -> Maybe Name
        names (TyConApp n _) = Just n 
        names _ = Nothing

        mkSortsZ3 :: M.Map Name Sort -> (Name, Type) -> Z3 (M.Map Name Sort)
        mkSortsZ3 m (n, (TyAlg n' dcs)) = do
            cons <- mapM (mkConstructorZ3 m) dcs
            nSymb <- mkStringSymbol n
            d <- mkDatatype nSymb cons
            return . M.insert n d $ m

mkConstructorZ3 :: M.Map Name Sort -> DataCon -> Z3 Constructor
--we need to do something to ensure all symbols are unique... adjust
mkConstructorZ3 d (DC (n, _, _, t)) = do
    n' <- mkStringSymbol n
    is_n <- mkStringSymbol ("is_" ++ n)
    s <- mapM mkStringSymbol . numFresh n (length t) $ []
    t' <- mapM (sortZ3 d) t

    mkConstructor n' is_n . map (\(s, t) -> (s, Just t, 0)) . zip s $ t'

exprZ3 :: M.Map Name Sort -> Expr -> Z3 AST
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
handleFunctionsZ3 _ (Var "I#" _) [Const c] = constZ3 c
handleFunctionsZ3 _ (Var "F#" _) [Const c] = constZ3 c
handleFunctionsZ3 _ (Var "D#" _) [Const c] = constZ3 c
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

-- SMT internal representation

{-- type Z3Name = String

data Stmt = ADecl Z3Name [Z3DCon]
          | CDecl Z3Name Z3Type
          | FDecl Z3Name [Z3Type] Z3Type
          | MAsrt Match Z3DCon
          deriving (Show, Eq)

data Z3DCon = Z3DC Z3Name [(Z3Name, Z3Type)]
            deriving (Show, Eq)

data Z3Type = Z3TyInt
            | Z3TyBool
            | Z3TyReal
            | Z3TyVar Z3Name -- Unfortunately seems like no function types :(
            deriving (Show, Eq)

data Match = MVar Z3Name
           | MFApp Z3Name [Z3Name]
           deriving (Show, Eq)

-- Core to SMT

mkZ3Type :: Type -> Z3Type
mkZ3Type (TyVar n) = Z3TyVar n
mkZ3Type TyRawInt  = Z3TyInt
-- mkZ3Type TyBool    = Z3TyBool
mkZ3Type TyRawFloat    = Z3TyReal
mkZ3Type otherwise = error $ "Cannot convert type {" ++ show otherwise ++ "}"

-- We want forced conversions here as ADTs in Z3 can't have higher order args.
mkZ3DC :: DataCon -> Z3DCon
mkZ3DC (name, tag, typ, args) = Z3DC name nts
  where nts = map (\(i, t) -> (name ++ "?D?" ++ show i, mkZ3Type t)) nas
        nas = zip [1..] args

mkZ3ADT :: Type -> Stmt
mkZ3ADT (TyAlg n dcs) = ADecl n (map mkZ3DC dcs)
mkZ3ADT otherwise     = error "Not an ADT"

mkADecls :: [Type] -> [Stmt]
mkADecls [] = []
mkADecls ((TyAlg n dcs):tv) = mkZ3ADT (TyAlg n dcs) : mkADecls tv
mkADecls (t:tv) = mkADecls tv  -- Skip the non-ADTs

-- Now we want to handle the function declarations
unTyFun :: Type -> ([Type], Type)
unTyFun (TyFun l r) = let (as, t) = unTyFun r in (l:as ,t)
unTyFun otherwise   = ([], otherwise)

cfDeclared :: [Stmt] -> Name -> Bool
cfDeclared [] n = False
cfDeclared ((CDecl cn t):ds) n = if cn == n then True else cfDeclared ds n
cfDeclared ((FDecl fn as t):ds) n = if fn == n then True else cfDeclared ds n
cfDeclared (d:ds) n = cfDeclared ds n

mkCDecl :: Name -> Type -> Stmt
mkCDecl n t = CDecl n (mkZ3Type t)

mkFDecl :: Name -> Type -> Stmt
mkFDecl n t = FDecl n zas zr
  where (as, r) = unTyFun t
        zas     = map mkZ3Type as
        zr      = mkZ3Type r

mkAsrts :: PC -> [Stmt]
mkAsrts [] = []
mkAsrts ((exp, (dc, args)):pcs) = e_asrt ++ mkAsrts pcs
  where (h:args) = unapp exp
        e_asrt   = case h of
            Var n t   -> case args of
                [] -> let cdecl  = mkCDecl n t
                          cmatch = MVar n
                          z3dc   = mkZ3DC dc
                      in [cdecl, MAsrt cmatch z3dc]
                as -> let fdecl    = mkFDecl n (typeOf exp)
                          -- argdecls = map (\a -> mkCDecl (n ++ "?" ++ a) (typeOf a)) args
                          fmatch   = []
                      in undefined
            DCon dc   -> []  -- Driven by structure otherwise.
            otherwise -> []
--}

{-
mkAsrts :: PC -> [Stmt]
mkAsrts [] = []
mkAsrts ((exp, alt):pcs) = e_asrt ++ mkAsrts pcs
  where (h:args) = unapp exp
        e_asrt   = case h of
            Var n t   -> []
            -- Var n t   -> let fname = n ++ "?F?" ++ (show $ length args)
            --              in 
            DCon dc t -> [] -- We rely on structure to drive execution.
            otherwise -> []
-}


{-
mkCFDecls :: [(Name, Expr)] -> [Stmt]
mkCFDecls [] = []
mkCFDecls ((n, (Lam b e t)):ev) = undefined
mkCFDecls ((n, e):ev) = CDecl n (mkZ3Type $ typeOf e) : mkCFDecls ev
-}

{-- mkSMTModels :: State -> [Stmt]
mkSMTModels (tv, ev, ex, pc) = ddecls ++ fdecls
  where ddecls = mkADecls $ M.elems tv
        fdecls = undefined

-- SMT to String


--REMOVE THIS
check :: Z3 ()
check = do
  _1 <- mkInteger 1
  _2 <- mkInteger 2
  return =<< assert =<< mkLe _1 _2 --}

