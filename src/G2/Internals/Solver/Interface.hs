{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Solver.Interface
    ( subModel
    , subVar
    , subVarFuncCall
    , checkConstraints
    , checkConstraintsWithSMTSorts
    , checkModel
    , checkModelWithSMTSorts
    ) where

import G2.Internals.Config.Config
import G2.Internals.Execution.NormalForms
import G2.Internals.Language hiding (Model)
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.PathConds as PC
import G2.Internals.Solver.ADTSolver
import G2.Internals.Solver.Converters
import G2.Internals.Solver.Language

import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M
import Data.Maybe

subModel :: State h t -> ([Expr], Expr, Maybe FuncCall)
subModel (State { expr_env = eenv
                , curr_expr = CurrExpr _ cexpr
                , input_ids = is
                , assert_ids = ais
                , type_classes = tc
                , model = m}) =
    let
        ais' = fmap (subVarFuncCall m eenv tc) ais
    in
    filterTC tc $ subVar m eenv tc (map Var is, cexpr, ais')

subVarFuncCall :: ExprModel -> ExprEnv -> TypeClasses -> FuncCall -> FuncCall
subVarFuncCall em eenv tc fc@(FuncCall {arguments = ars}) =
    subVar em eenv tc $ fc {arguments = filter (not . isTC tc) ars}

subVar :: (ASTContainer m Expr) => ExprModel -> ExprEnv -> TypeClasses -> m -> m
subVar em eenv tc = modifyContainedVars (subVar' em eenv tc) . filterTC tc

subVar' :: ExprModel -> ExprEnv -> TypeClasses -> Expr -> Expr
subVar' em eenv tc v@(Var (Id n _)) =
    case M.lookup n em of
        Just e -> filterTC tc e
        Nothing -> case E.lookup n eenv of
            Just e -> if (isExprValueForm e eenv && notLam e) || isApp e || isVar e then subVar' em eenv tc $ filterTC tc e else v
            Nothing -> v
subVar' _ _ _ e = e

notLam :: Expr -> Bool
notLam (Lam _ _) = False
notLam _ = True

isApp :: Expr -> Bool
isApp (App _ _) = True
isApp _ = False

isVar :: Expr -> Bool
isVar (Var _) = True
isVar _ = False

modifyContainedVars :: ASTContainer m Expr => (Expr -> Expr) -> m -> m
modifyContainedVars f = modifyContainedASTs (modifyVars' f [])

modifyVars' :: (Expr -> Expr) -> [Id] -> Expr -> Expr
modifyVars' f is v@(Var i) = if i `elem` is then v else modifyVars' f (i:is) (f v)
modifyVars' f is e = modifyChildren (modifyVars' f is) e

filterTC :: ASTContainer m Expr => TypeClasses -> m -> m
filterTC tc = modifyASTsFix (filterTC' tc)

filterTC' :: TypeClasses -> Expr -> Expr
filterTC' tc a@(App e e') =
    case tcCenter tc $ typeOf e' of
        True -> e 
        False -> a
filterTC' _ e = e

tcCenter :: TypeClasses -> Type -> Bool
tcCenter tc (TyConApp n _) = isTypeClassNamed n tc
tcCenter tc (TyFun t _) = tcCenter tc t
tcCenter _ _ = False

isTC :: TypeClasses -> Expr -> Bool
isTC tc (Var (Id _ (TyConApp n _))) = isTypeClassNamed n tc
isTC _ _ = False

-- | checkConstraints
-- Checks if the path constraints are satisfiable
checkConstraints :: SMTConverter ast out io -> io -> State h t -> IO Result
checkConstraints con io s = do
    case checkConsistency (known_values s) (type_env s) (path_conds s) of
        Just True -> return SAT
        Just False -> return UNSAT
        _ -> do
            -- putStrLn "------"
            -- putStrLn $ "PC        = " ++ (pprPathsStr . PC.toList $ path_conds s)
            -- putStrLn $ "PC unsafe = " ++ (pprPathsStr . PC.toList . unsafeElimCast $ path_conds s)
            checkConstraints' con io s

checkConstraints' :: SMTConverter ast out io -> io -> State h t -> IO Result
checkConstraints' con io s = do
    -- let s' = filterTEnv . simplifyPrims $ s
    let s' = s {path_conds = unsafeElimCast . simplifyPrims $ path_conds s}

    let headers = toSMTHeaders s'
    let formula = toSolver con headers

    checkSat con io formula

checkConstraintsWithSMTSorts :: Config -> SMTConverter ast out io -> io -> State h t -> IO Result
checkConstraintsWithSMTSorts config con io s = do
    let tenv = filterTEnv (type_env s) (path_conds s)
    let pc = unsafeElimCast . simplifyPrims $ path_conds s

    let (tenv', pc', _) = case smt config of
                                Z3 -> elimPolymorphic tenv pc () (name_gen s)
                                CVC4 -> (tenv, pc, ())

    let s' = s { type_env = tenv'
               , path_conds = pc' }

    let headers = toSMTHeadersWithSMTSorts s'
    let formula = toSolver con headers

    checkSat con io formula

elimPolymorphic :: (ASTContainer m Type, Named m) => TypeEnv -> PC.PathConds -> m -> NameGen -> (TypeEnv, PC.PathConds, m)
elimPolymorphic tenv pc e ng =
    let
       ts = nub $ evalASTs nonTyVarTyConApp (tenv, pc)
       (tenv', nm, tm) = genNewAlgDataTy tenv M.empty ts HM.empty [] ng

       pc' = elimTyForAll $ foldr (uncurry replaceASTs) pc tm
       e' = elimTyForAll $ foldr (uncurry replaceASTs) e tm
    in
    renames nm (tenv', pc', e')

nonTyVarTyConApp :: Type -> [Type]
nonTyVarTyConApp t@(TyConApp _ ts) = if not $ any isTyVar ts then [t] else []
nonTyVarTyConApp _ = []

genNewAlgDataTy :: TypeEnv -> TypeEnv -> [Type] -> HM.HashMap Name Name -> [(Type, Type)] -> NameGen -> (TypeEnv, HM.HashMap Name Name, [(Type, Type)])
genNewAlgDataTy _ tenv [] nm tm _ = (tenv, nm, tm)
genNewAlgDataTy tenv ntenv ((TyConApp n []):xs) nm tm ng =
    let
        adt = case M.lookup n tenv of
                    Just a -> a
                    Nothing -> error $ "ADT not found in genNewAlgDataTy" ++ show n

        ntenv' = M.insert n adt ntenv
    in
    genNewAlgDataTy tenv ntenv' xs nm tm ng
genNewAlgDataTy tenv ntenv (t@(TyConApp n ts):xs) nm tm ng =
    let
        adt = case M.lookup n tenv of
                    Just a -> a
                    Nothing -> error $ "ADT not found in genNewAlgDataTy" ++ show n
        tyv = map (TyVar . flip Id TYPE) $ bound_names adt
        tyRep = (t, TyConApp n []):zip tyv ts

        adt' = adt {bound_names = []}

        -- ns = nub $ names adt
        -- (ns', ng') = renameAll ns ng
        (n', ng') = freshSeededName n ng
        nns = HM.singleton n n'

        adt'' = renames nns $ foldr (uncurry replaceASTs) adt' tyRep

        adt''' = elimTyForAll adt''

        ntenv' = M.insert n' adt''' ntenv
    in
    genNewAlgDataTy tenv ntenv' xs (HM.union nns nm) (tm ++ tyRep) ng'
genNewAlgDataTy _ _ _ _ _ _ = error "Unhandled type in genNewAlgDataTy"


elimTyForAll :: (ASTContainer m Type) => m -> m
elimTyForAll = modifyASTs elimTyForAll'

elimTyForAll' :: Type -> Type
elimTyForAll' (TyForAll _ t) = t
elimTyForAll' t = t

-- | checkModel
-- Checks if the constraints are satisfiable, and returns a model if they are
checkModel :: SMTConverter ast out io -> io -> State h t -> IO (Result, Maybe ExprModel)
checkModel con io s = do
    -- let s' = filterTEnv . simplifyPrims $ s
    let s' = s {path_conds = simplifyPrims $ path_conds s}
    return . fmap liftCasts =<< checkModel' con io (symbolic_ids s') s'

-- | checkModel'
-- We split based on whether we are evaluating a ADT or a literal.
-- ADTs can be solved using our efficient addADTs, while literals require
-- calling an SMT solver.
checkModel' :: SMTConverter ast out io -> io -> [Id] -> State h t -> IO (Result, Maybe ExprModel)
checkModel' _ _ [] s = do
    return (SAT, Just $ model s)
-- We can't use the ADT solver when we have a Boolean, because the RHS of the
-- DataAlt might be a primitive.
checkModel' con io (Id n t@(TyConApp tn ts):is) s
    | t /= tyBool (known_values s)  =
    do
        let (r, is', s') = addADTs n tn ts s

        let is'' = filter (\i -> i `notElem` is && (idName i) `M.notMember` (model s)) is'

        case r of
            SAT -> checkModel' con io (is ++ is'') s'
            r' -> return (r', Nothing)
checkModel' con io (i:is) s = do
    (m, av) <- getModelVal con io i Nothing s
    case m of
        Just m' -> checkModel' con io is (s {model = M.union m' (model s), arbValueGen = av})
        Nothing -> return (UNSAT, Nothing)

getModelVal :: SMTConverter ast out io -> io -> Id -> Maybe Config -> State h t -> IO (Maybe ExprModel, ArbValueGen)
getModelVal con io (Id n _) config s = do
    let (Just (Var (Id n' t))) = E.lookup n (expr_env s)
 
    let pc = PC.scc (known_values s) [n] (path_conds s)
    let s' = s {path_conds = pc }

    case PC.null pc of
                True -> 
                    let
                        (e, av) = arbValue t (type_env s) (arbValueGen s)
                    in
                    return (Just $ M.singleton n' e, av) 
                False -> do
                    e <- checkNumericConstraints con io config s'
                    return (e, arbValueGen s)

checkNumericConstraints :: SMTConverter ast out io -> io -> Maybe Config -> State h t -> IO (Maybe ExprModel)
checkNumericConstraints con io config s = do
    let headers = case maybe False smtADTs config of
                        False -> toSMTHeaders s
                        True -> toSMTHeadersWithSMTSorts s
    let formula = toSolver con headers

    let vs = map (\(n', srt) -> (nameToStr n', srt)) . pcVars . PC.toList $ path_conds s

    (_, m) <- checkSatGetModel con io formula headers vs

    let m' = fmap modelAsExpr m

    case m' of
        Just m'' -> return $ Just m''
        Nothing -> return Nothing

-- | addADTs
-- Determines an ADT based on the path conds.  The path conds form a witness.
-- In particular, refer to findConsistent in Solver/ADTSolver.hs
addADTs :: Name -> Name -> [Type] -> State h t -> (Result, [Id], State h t)
addADTs n tn ts s =
    let
        pc = PC.scc (known_values s) [n] (path_conds s)

        dcs = findConsistent (known_values s) (type_env s) pc

        eenv = expr_env s

        (dc, nst) = case dcs of
                Just (fdc:_) ->
                    let
                        -- We map names over the arguments of a DataCon, to make sure we have the correct
                        -- number of undefined's.
                        -- In the case of a PrimCon, we still need one undefined if the primitive is not
                        -- in the type env
                        ts'' = case exprInCasts fdc of
                            Data (DataCon _ _ ts') -> map (const $ Name "a" Nothing 0 Nothing) ts'
                            _ -> [Name "b" Nothing 0 Nothing]

                        (ns, _) = childrenNames n ts'' (name_gen s)

                        vs = map (\n' -> 
                                case  E.lookup n' eenv of
                                    Just e -> e
                                    Nothing -> Prim Undefined TyBottom) ns
                        is = mapMaybe (varId) vs
                    in
                    (mkApp $ fdc:vs, is)
                _ -> error "Unusable DataCon in addADTs"

        m = M.insert n dc (model s)

        (bse, av) = arbValue (TyConApp tn ts) (type_env s) (arbValueGen s)

        m' = M.insert n bse m
    in
    case PC.null pc of
        True -> (SAT, [], s {model = M.union m' (model s), arbValueGen = av})
        False -> case not . null $ dcs of
                    True -> (SAT, nst, s {model = M.union m (model s)})
                    False -> (UNSAT, [], s)

-- | checkModelWithSMTSorts
-- Checks if the constraints are satisfiable, and returns a model if they are
checkModelWithSMTSorts :: SMTConverter ast out io -> io -> Config -> State h t -> IO (Result, Maybe ExprModel)
checkModelWithSMTSorts con io config s@(State {expr_env = eenv}) = do
    let tenv = filterTEnv (type_env s) (path_conds s)
    let cexpr = earlySubVar eenv $ curr_expr s
    let pc = unsafeElimCast . earlySubVar eenv . simplifyPrims $ path_conds s

    let (tenv', pc', cexpr') = case smt config of
                                    Z3 -> elimPolymorphic tenv pc cexpr (name_gen s)
                                    CVC4 -> (tenv, pc, cexpr)

    let s' = s { type_env = tenv'
               , curr_expr = cexpr'
               , path_conds = pc' }
    return . fmap liftCasts =<< checkModelWithSMTSorts' con io (symbolic_ids s') config s'

checkModelWithSMTSorts' :: SMTConverter ast out io -> io -> [Id] -> Config -> State h t -> IO (Result, Maybe ExprModel)
checkModelWithSMTSorts' _ _ [] _ s = do
    return (SAT, Just $ model s)
checkModelWithSMTSorts' con io (i:is) config s = do
    (m, av) <- getModelVal con io i (Just config) s
    case m of
        Just m' -> checkModelWithSMTSorts' con io is config (s {model = M.union m' (model s), arbValueGen = av})
        Nothing -> return (UNSAT, Nothing)

-- Narrow the TypeEnv to the types relevant to the given PathConds
filterTEnv :: TypeEnv -> PC.PathConds -> TypeEnv
filterTEnv tenv pc =
    let
        ns = filter (typeEnvName tenv) $ nub $ names pc
    in
    filterTEnv' ns ns tenv-- M.filterWithKey (\k _ -> k `elem` ns) tenv

filterTEnv' :: [Name] -> [Name] -> TypeEnv -> TypeEnv
filterTEnv' [] keep tenv =
    M.filterWithKey (\k _ -> k `elem` keep) tenv
filterTEnv' search keep tenv =
    let
        new = filter (not . flip elem keep) 
            $ filter (typeEnvName tenv) 
            $ names 
            $ mapMaybe (flip M.lookup tenv) search
    in
    filterTEnv' new (new ++ keep) tenv

typeEnvName :: TypeEnv -> Name -> Bool
typeEnvName tenv = flip elem (M.keys tenv)

earlySubVar :: (ASTContainer m Expr) => ExprEnv -> m -> m
earlySubVar eenv = modifyASTs (earlySubVar' eenv)

earlySubVar' :: ExprEnv -> Expr -> Expr
earlySubVar' eenv v@(Var (Id n _)) =
    case E.deepLookup n eenv of
        Just v' -> v'
        Nothing -> v
earlySubVar' _ e = e

-- filterTEnv :: State -> State
-- filterTEnv s@State { type_env = tenv} =
--     if tenv == tenv'
--       then s { type_env = tenv }
--       else filterTEnv (s { type_env = tenv' })
--   where
--     tenv' = M.filter (filterTEnv' tenv) tenv

-- filterTEnv' :: TypeEnv -> AlgDataTy -> Bool
-- filterTEnv' tenv (DataTyCon _ dc) = length dc > 0 && not (any (filterTEnv'' tenv) dc)
-- filterTEnv' _ _ = False

-- filterTEnv'' :: TypeEnv -> DataCon -> Bool
-- filterTEnv'' tenv (DataCon _ _ ts) = any (hasFuncType) ts || any (notPresent tenv) ts
-- filterTEnv'' _ _ = False

-- notPresent :: TypeEnv -> Type -> Bool
-- notPresent tenv (TyConApp n _) = n `M.notMember` tenv
-- notPresent _ _ = False

{- TODO: This function is hacky- would be better to correctly handle typeclasses... -}
simplifyPrims :: ASTContainer t Expr => t -> t
simplifyPrims = modifyASTs simplifyPrims'

simplifyPrims' :: Expr -> Expr
simplifyPrims' (App (App (App (Prim Negate t) _) _) a) = App (Prim Negate t) a
simplifyPrims' (App (App (App (App (Prim p t) _) _) a) b) = App (App (Prim p t) a) b
simplifyPrims' e = e
