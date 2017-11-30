{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.SMT.Interface
    ( subModel
    , checkConstraints
    , checkModel
    ) where

import G2.Internals.Language hiding (Model)
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.PathConds as PC
import G2.Internals.SMT.Converters
import G2.Internals.SMT.Language

import qualified Data.Map as M
import Data.Maybe

import G2.Lib.Printers

subModel :: State -> ([Expr], Expr)
subModel (State { curr_expr = CurrExpr _ cexpr
                , input_ids = is
                , model = m}) =
    subVar m (map Var is, cexpr)

subVar :: (ASTContainer m Expr) => ExprModel -> m -> m
subVar em = modifyASTs (subVar' em)

subVar' :: ExprModel -> Expr -> Expr
subVar' em v@(Var (Id n _)) =
    case M.lookup n em of
        Just e -> e
        Nothing -> v
subVar' _ e = e

-- | checkConstraints
-- Checks if the path constraints are satisfiable
checkConstraints :: SMTConverter ast out io -> io -> State -> IO Result
checkConstraints con io s = do
    case PC.checkConsistency (type_env s) (path_conds s) of
        Just True -> return SAT
        Just False -> return UNSAT
        _ -> do
            -- putStrLn "------"
            -- putStrLn . pprPathsStr . PC.toList $ path_conds s
            checkConstraints' con io s

checkConstraints' :: SMTConverter ast out io -> io -> State -> IO Result
checkConstraints' con io s = do
    let s' = filterTEnv . simplifyPrims $ s

    let headers = toSMTHeaders s'
    let formula = toSolver con headers

    checkSat con io formula

-- | checkModel
-- Checks if the constraints are satisfiable, and returns a model if they are
checkModel :: SMTConverter ast out io -> io -> State -> IO (Result, Maybe ExprModel)
checkModel con io s = do
    let s' = filterTEnv . simplifyPrims $ s

    checkModel' con io (input_ids s') s'

-- | checkModel'
-- We split based on whether we are evaluating a ADT or a literal.
-- ADTs can be solved using our efficient addADTs, while literals require
-- calling an SMT solver.
checkModel' :: SMTConverter ast out io -> io -> [Id] -> State -> IO (Result, Maybe ExprModel)
checkModel' _ _ [] s = do
    return (SAT, Just $ model s)
checkModel' con io (Id n (TyConApp tn _):is) s = do
    let (r, is', s') = addADTs n tn s

    let is'' = filter (\i -> i `notElem` is && (idName i) `M.notMember` (model s)) is'

    case r of
        SAT -> checkModel' con io (is ++ is'') s'
        r' -> return (r', Nothing)
checkModel' con io ((Id n _):is) s = do
    let (Just (Var i')) = E.lookup n (expr_env s)
 
    let pc = PC.scc [n] (path_conds s)

    let s' = s {path_conds = if PC.null pc then PC.fromList [PCExists i'] else pc }

    let headers = toSMTHeaders s'
    let formula = toSolver con headers

    let vs = map (\(n', srt) -> (nameToStr n', srt)) . pcVars . PC.toList $ path_conds s'

    (_, m) <- checkSatGetModel con io formula headers vs

    let m' = fmap modelAsExpr m

    case m' of
        Just m'' -> checkModel' con io is (s {model = M.union m'' (model s)})
        Nothing -> return (UNSAT, Nothing)

-- | addADTs
-- Determines an ADT based on the path conds.  The path conds form a witness.
-- In particular, refer to findConsistent in Language/PathConds.hs
addADTs :: Name -> Name -> State -> (Result, [Id], State)
addADTs n tn s =
    let
        pc = PC.scc [n] (path_conds s)

        dcs = PC.findConsistent (type_env s) pc

        eenv = expr_env s

        (ns, _) = childrenNames n [] (name_gen s)
        (dc, nst) = case dcs of
                Just (fdc:_) ->
                    let
                        vs = mapMaybe (flip E.lookup eenv) ns
                        is = map (\(Var i) -> i) vs
                    in
                    (mkApp $ (Data fdc):vs, is)
                _ -> error "Unusable DataCon in addADTs"

        m = M.insert n dc (model s)

        (Just (base:_)) = fmap baseDataCons $ getDataCons tn (type_env s)
        m' = M.insert n (Data base) m
    in
    case PC.null pc of
        True -> (SAT, [], s {model = M.union m' (model s)})
        False -> case not . null $ dcs of
                    True -> (SAT, nst, s {model = M.union m (model s)})
                    False -> (UNSAT, [], s)

-- Remove all types from the type environment that contain a function
filterTEnv :: State -> State
filterTEnv s@State { type_env = tenv} =
    if tenv == tenv'
      then s { type_env = tenv }
      else filterTEnv (s { type_env = tenv' })
  where
    tenv' = M.filter (filterTEnv' tenv) tenv

filterTEnv' :: TypeEnv -> AlgDataTy -> Bool
filterTEnv' tenv (DataTyCon _ dc) = length dc > 0 && not (any (filterTEnv'' tenv) dc)
filterTEnv' _ _ = False

filterTEnv'' :: TypeEnv -> DataCon -> Bool
filterTEnv'' tenv (DataCon _ _ ts) = any (hasFuncType) ts || any (notPresent tenv) ts
filterTEnv'' _ _ = False

notPresent :: TypeEnv -> Type -> Bool
notPresent tenv (TyConApp n _) = n `M.notMember` tenv
notPresent _ _ = False

{- TODO: This function is hacky- would be better to correctly handle typeclasses... -}
simplifyPrims :: ASTContainer t Expr => t -> t
simplifyPrims = modifyASTs simplifyPrims'

simplifyPrims' :: Expr -> Expr
simplifyPrims' (App (App (App (Prim Negate t) _) _) a) = App (Prim Negate t) a
simplifyPrims' (App (App (App (App (Prim p t) _) _) a) b) = App (App (Prim p t) a) b
simplifyPrims' e = e
