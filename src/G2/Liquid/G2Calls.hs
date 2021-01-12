{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.G2Calls ( GathererReducer (..)
                         , checkAbstracted
                         , reduceCalls
                         , reduceFuncCall
                         , mapAccumM) where

import G2.Config
import G2.Execution
import G2.Interface
import G2.Language as G2
import qualified G2.Language.ExprEnv as E
import G2.Liquid.Helpers
import G2.Liquid.LHReducers
import G2.Liquid.SpecialAsserts
import G2.Liquid.Types
import G2.Solver

import G2.Lib.Printers

import Control.Monad
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import qualified Data.Map as M
import Data.Maybe

import Data.Monoid

import Debug.Trace
import Control.Exception
-------------------------------
-- Check Abstracted
-------------------------------
-- Checks if the abstracted functions actually deviate from the real function behavior.
-- If they do not, they can simply be eliminated from the state.

-- The result of a call to checkAbstracted'.  Either:
-- (1) the function does need to be abstract, and we get the actual result of executing the function call. 
-- (2) the function does not need to be abstract
data AbstractedRes = AbstractRes Abstracted Model
                   | NotAbstractRes

toAbstracted :: AbstractedRes -> Maybe Abstracted
toAbstracted (AbstractRes a _) = Just a
toAbstracted _ = Nothing

toModel :: AbstractedRes -> Maybe Model
toModel (AbstractRes _ m) = Just m
toModel _ = Nothing

-- | Checks if abstracted functions actually had to be abstracted.
checkAbstracted :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> Config -> Id -> Bindings -> ExecRes LHTracker -> IO (ExecRes AbstractedInfo)
checkAbstracted solver simplifier config init_id bindings er@(ExecRes{ final_state = s@State { track = lht }
                                                                     , conc_args = inArg
                                                                     , conc_out = ex }) = do
    -- Get `Abstracted`s for the abstracted functions 
    let check = checkAbstracted' solver simplifier (sharing config) s bindings
    abstractedR <- mapM check (abstract_calls lht)
    let abstracted' = mapMaybe toAbstracted $ abstractedR
        models = mapMaybe toModel $ abstractedR

    -- Get an `Abstracted` for the initial call
    let init_call = FuncCall (idName init_id) inArg ex
    abs_init <- getAbstracted solver simplifier (sharing config) s bindings init_call
    let init_model = snd abs_init

    -- Get an `Abstracted` for the violated function (if it exists)
    abs_viol <- case violated er of
                  Just v -> return . Just =<<
                              getAbstracted solver simplifier (sharing config) s bindings v
                  Nothing -> return Nothing
    let viol_model = maybeToList $ fmap snd abs_viol
        abs_info = AbstractedInfo { init_call = fst abs_init
                                  , abs_violated = fmap fst abs_viol
                                  , abs_calls = abstracted'
                                  , ai_all_calls = all_calls lht }

    return $ er { final_state = s { track = abs_info
                                  , model = foldr HM.union (model s) (init_model:viol_model ++ models) }
                }

checkAbstracted' :: (Solver solver, Simplifier simplifier)
                 => solver
                 -> simplifier
                 -> Sharing
                 -> State LHTracker
                 -> Bindings
                 -> FuncCall
                 -> IO AbstractedRes
checkAbstracted' solver simplifier share s bindings abs_fc@(FuncCall { funcName = n, arguments = ars, returns = r })
    | Just e <- E.lookup n $ expr_env s = do
        let 
            e' = mkApp $ Var (Id n (typeOf e)):ars

            ds = deepseq_walkers bindings
            strict_call = maybe e' (fillLHDictArgs ds) $ mkStrict_maybe ds e'

        -- We leave assertions in the code, and set true_assert to false so we can
        -- tell if an assertion was violated.
        -- If an assertion is violated, it means that the function did not need to be abstracted,
        -- but does need to be in `assert_ids` .
        -- We eliminate all assumes, except those blocking calls to library functions.
        -- See [BlockErrors] in G2.Liquid.SpecialAsserts
        let s' = elimAssumesExcept
               . pickHead
               . elimSymGens (arb_value_gen bindings)
               . modelToExprEnv $
                    s { curr_expr = CurrExpr Evaluate strict_call
                      , track = False }

        (er, _) <- runG2WithSomes 
                        (SomeReducer (StdRed share solver simplifier :<~ HitsLibError))
                        (SomeHalter SWHNFHalter)
                        (SomeOrderer NextOrderer)
                        solver simplifier emptyMemConfig s' bindings

        case er of
            [ExecRes
                {
                    final_state = (State { curr_expr = CurrExpr _ ce, model = m, track = t})
                }] -> case not $ ce `eqUpToTypes` r of
                        True ->
                            return $ AbstractRes 
                                        ( Abstracted { abstract = abs_fc
                                                     , real = abs_fc { returns = ce }
                                                     , hits_lib_err_in_real = t }
                                        ) m
                        False -> return NotAbstractRes
            [] -> do undefined -- ^ We hit an error in a library function
                     return $ AbstractRes 
                              ( Abstracted { abstract = abs_fc
                                           , real = abs_fc { returns = Prim Error TyUnknown }
                                           , hits_lib_err_in_real = True
                                           , func_calls_in_real = [] }
                              ) (model s)
            _ -> error $ "checkAbstracted': Bad return from runG2WithSomes"
    | otherwise = error $ "checkAbstracted': Bad lookup in runG2WithSomes"

getAbstracted :: (Solver solver, Simplifier simplifier)
              => solver
              -> simplifier
              -> Sharing 
              -> State LHTracker
              -> Bindings
              -> FuncCall
              -> IO (Abstracted, Model)
getAbstracted solver simplifier share s bindings abs_fc@(FuncCall { funcName = n, arguments = ars, returns = r })
    | Just e <- E.lookup n $ expr_env s = do
        let 
            e' = mkApp $ Var (Id n (typeOf e)):ars

            ds = deepseq_walkers bindings
            strict_call = maybe e' (fillLHDictArgs ds) $ mkStrict_maybe ds e'

        let s' = mkAssertsTrue (known_values s)
               . elimAssumesExcept
               . pickHead
               . elimSymGens (arb_value_gen bindings)
               . modelToExprEnv $
                    s { curr_expr = CurrExpr Evaluate strict_call
                      , track = ([] :: [FuncCall], False)}

        let pres = HS.fromList $ names s' ++ names bindings
        (er, bindings') <- runG2WithSomes 
                              (SomeReducer (StdRed share solver simplifier :<~ HitsLibErrorGatherer))
                              (SomeHalter SWHNFHalter)
                              (SomeOrderer NextOrderer)
                              solver simplifier
                              (emptyMemConfig { pres_func = \_ _ _ -> pres })
                              s' bindings

        case er of
            [ExecRes
                {
                    final_state = fs@(State { curr_expr = CurrExpr _ ce, track = (gfc, hle), model = m})
                }] -> do
                  let fs' = modelToExprEnv fs
                  (bindings'', gfc') <- reduceFuncCallMaybeList solver simplifier share bindings' fs' gfc
                  return $ ( Abstracted { abstract = abs_fc
                                        , real = abs_fc { returns = ce }
                                        , hits_lib_err_in_real = hle
                                        , func_calls_in_real = gfc' }
                                , m)
            _ -> error $ "checkAbstracted': Bad return from runG2WithSomes"
    | otherwise = error $ "getAbstracted: Bad lookup in runG2WithSomes"

data HitsLibError = HitsLibError

instance Reducer HitsLibError () Bool where
    initReducer _ _ = ()
    redRules r _ s@(State { curr_expr = CurrExpr _ ce }) b =
        case ce of
            Tick t _ 
              | t == assumeErrorTickish ->
                  return (NoProgress, [(s { track = True }, ())], b, r)
            _ -> return (NoProgress, [(s, ())], b, r)

data GathererReducer = Gatherer

instance Reducer GathererReducer () [FuncCall] where
    initReducer _ _ = ()

    redRules gr _ s@(State { curr_expr = CurrExpr Evaluate (e@(Assume (Just fc) _ _))
                           , track = tr
                           }) b =
        let
          s' = s { curr_expr = CurrExpr Evaluate e
                 , track = fc:tr}
        in
        return (Finished, [(s', ())], b, gr) 
    redRules gr _ s@(State { curr_expr = CurrExpr Evaluate (e@(G2.Assert (Just fc) _ _))
                           , track = tr
                           }) b =
        let
          s' = s { curr_expr = CurrExpr Evaluate e
                 , track = fc:tr}
        in
        return (Finished, [(s', ())], b, gr) 
    redRules gr _ s b = return (Finished, [(s, ())], b, gr)

data HitsLibErrorGathererReducer = HitsLibErrorGatherer

instance Reducer HitsLibErrorGathererReducer () ([FuncCall], Bool) where
    initReducer _ _ = ()

    redRules gr _ s@(State { curr_expr = CurrExpr Evaluate (e@(Assume (Just fc) _ _))
                           , track = (tr, hle)
                           }) b =
        let
          s' = s { curr_expr = CurrExpr Evaluate e
                 , track = (fc:tr, hle)}
        in
        return (Finished, [(s', ())], b, gr) 
    redRules gr _ s@(State { curr_expr = CurrExpr Evaluate (e@(G2.Assert (Just fc) _ _))
                           , track = (tr, hle)
                           }) b =
        let
          s' = s { curr_expr = CurrExpr Evaluate e
                 , track = (fc:tr, hle)}
        in
        return (Finished, [(s', ())], b, gr) 
    redRules r _ s@(State { curr_expr = CurrExpr _ ce, track = (glc, _) }) b =
        case ce of
            Tick t _ 
              | t == assumeErrorTickish ->
                  return (NoProgress, [(s { track = (glc, True) }, ())], b, r)
            _ -> return (NoProgress, [(s, ())], b, r)


-- | Remove all @Assume@s from the given `Expr`, unless they have a particular @Tick@
elimAssumesExcept :: ASTContainer m Expr => m -> m
elimAssumesExcept = modifyASTs elimAssumesExcept'

elimAssumesExcept' :: Expr -> Expr
elimAssumesExcept' a@(Assume _ (Tick t _) e)
    | t == assumeErrorTickish = Tick t e
    | otherwise = e
elimAssumesExcept' (Assume _ _ e) = e
elimAssumesExcept' e = e


-------------------------------
-- Reduce Calls
-------------------------------
-- Reduces the arguments and results of the violated and abstracted functions to normal form.

reduceCalls :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> Config -> Bindings -> ExecRes LHTracker -> IO (Bindings, ExecRes LHTracker)
reduceCalls solver simplifier config bindings er = do
    (bindings', er') <- reduceViolated solver simplifier (sharing config) bindings er
    (bindings'', er'') <- reduceAbstracted solver simplifier (sharing config) bindings' er'
    (bindings''', er''') <- reduceAllCalls solver simplifier (sharing config) bindings'' er''

    return (bindings''', er''')

reduceViolated :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> Sharing -> Bindings -> ExecRes LHTracker -> IO (Bindings, ExecRes LHTracker)
reduceViolated solver simplifier share bindings er@(ExecRes { final_state = s, violated = Just v }) = do
    let red = SomeReducer (StdRed share solver simplifier :<~| RedArbErrors)
    (bindings', v') <- reduceFuncCall share red solver simplifier s bindings v
    -- putStrLn $ "v = " ++ show v
    -- putStrLn $ "v' = " ++ show v'
    return (bindings', er { violated = Just v' })
reduceViolated _ _ _ b er = return (b, er) 

reduceAbstracted :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> Sharing -> Bindings -> ExecRes LHTracker -> IO (Bindings, ExecRes LHTracker)
reduceAbstracted solver simplifier share bindings
                er@(ExecRes { final_state = (s@State { track = lht}) }) = do
    let red = SomeReducer (StdRed share solver simplifier :<~| RedArbErrors)
        fcs = abstract_calls lht

    (bindings', fcs') <- mapAccumM (reduceFuncCall share red solver simplifier s) bindings fcs

    return (bindings', er { final_state = s { track = lht { abstract_calls = fcs' } }})

reduceAllCalls :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> Sharing -> Bindings -> ExecRes LHTracker -> IO (Bindings, ExecRes LHTracker)
reduceAllCalls solver simplifier share bindings
                er@(ExecRes { final_state = (s@State { track = lht}) }) = do
    let fcs = all_calls lht

    (bindings', fcs') <- reduceFuncCallMaybeList solver simplifier share bindings s fcs

    -- (bindings', fcs') <- mapAccumM (reduceFuncCallMaybe share red solver simplifier s) bindings fcs

    return (bindings', er { final_state = s { track = lht { all_calls = fcs' } }})

reduceFuncCallMaybeList :: ( ASTContainer t Expr
                           , ASTContainer t Type
                           , Named t
                           , Show t
                           , Solver solver
                           , Simplifier simplifier) => solver -> simplifier -> Sharing -> Bindings -> State t -> [FuncCall] -> IO (Bindings, [FuncCall])
reduceFuncCallMaybeList solver simplifier share bindings s fcs = do
    let red = SomeReducer (StdRed share solver simplifier :<~| RedArbErrors)
    (b', fcs') <- mapAccumM (\b fc -> do
                                  b_fc <- reduceFuncCallMaybe share red solver simplifier s b fc
                                  case b_fc of
                                      Just (b', fc') -> return (b', Just fc')
                                      Nothing -> return (b, Nothing)) bindings fcs
    return (b', catMaybes fcs')

reduceFuncCall :: ( Solver solver
                  , Simplifier simp
                  , ASTContainer t Expr
                  , ASTContainer t Type
                  , Show t
                  , Named t)
               => Sharing -> SomeReducer t -> solver -> simp -> State t -> Bindings -> FuncCall -> IO (Bindings, FuncCall)
reduceFuncCall share red solver simplifier s bindings fc@(FuncCall { arguments = ars, returns = r }) = do
    -- (bindings', red_ars) <- mapAccumM (reduceFCExpr share (red <~ SomeReducer (Logger "arg")) solver simplifier s) bindings ars
    -- (bindings'', red_r) <- reduceFCExpr share (red <~ SomeReducer (Logger "ret")) solver simplifier s bindings' r
    (bindings', red_ars) <- mapAccumM (reduceFCExpr share red solver simplifier s) bindings ars
    (bindings'', red_r) <- reduceFCExpr share red solver simplifier s bindings' r

    return (bindings'', fc { arguments = red_ars, returns = red_r })

reduceFCExpr :: ( Solver solver
                , Simplifier simp
                , ASTContainer t Expr
                , ASTContainer t Type
                , Show t
                , Named t)
             => Sharing -> SomeReducer t -> solver -> simp -> State t -> Bindings -> Expr -> IO (Bindings, Expr)
reduceFCExpr share reducer solver simplifier s bindings e 
    | not . isTypeClass (type_classes s) $ (typeOf e)
    , ds <- deepseq_walkers bindings
    , Just strict_e <-  mkStrict_maybe ds e  = do
        let 
            e' = fillLHDictArgs ds strict_e

        let s' = elimAssumes
               . elimAsserts
               . pickHead
               . elimSymGens (arb_value_gen bindings)
               . modelToExprEnv $
                   s { curr_expr = CurrExpr Evaluate e'}

        (er, bindings') <- runG2WithSomes 
                              reducer
                              (SomeHalter SWHNFHalter)
                              (SomeOrderer NextOrderer)
                              solver simplifier emptyMemConfig s' bindings
        case er of
            [er'] -> do
                let (CurrExpr _ ce) = curr_expr . final_state $ er'
                return (bindings { name_gen = name_gen bindings' }, ce)
            _ -> error $ "reduceAbstracted: Bad reduction"
    | otherwise = return (bindings, redVar (expr_env s) e) 


reduceFuncCallMaybe :: ( Solver solver
                       , Simplifier simp
                       , ASTContainer t Expr
                       , ASTContainer t Type
                       , Show t
                       , Named t)
                    => Sharing -> SomeReducer t -> solver -> simp -> State t -> Bindings -> FuncCall -> IO (Maybe (Bindings, FuncCall))
reduceFuncCallMaybe share red solver simplifier s bindings fc@(FuncCall { arguments = ars, returns = r }) = do
    (bindings', red_ars)  <- mapAccumM (reduceFCExpr share red solver simplifier s) bindings ars
    (bindings'', red_r) <- reduceFCExpr share red solver simplifier s bindings' r

    return $ Just (bindings'', fc { arguments = red_ars, returns = red_r })

reduceFCExprMaybe :: ( Solver solver
                     , Simplifier simp
                     , ASTContainer t Expr
                     , ASTContainer t Type
                     , Named t)
                  => Sharing -> SomeReducer t -> solver -> simp -> State t -> Bindings -> Expr -> IO (Maybe (Bindings, Expr))
reduceFCExprMaybe share reducer solver simplifier s bindings e 
    | not . isTypeClass (type_classes s) $ (typeOf e)
    , ds <- deepseq_walkers bindings
    , Just strict_e <-  mkStrict_maybe ds e  = do
        let 
            e' = fillLHDictArgs ds strict_e

        let s' = elimAssumes
               . elimAsserts
               . pickHead
               . elimSymGens (arb_value_gen bindings)
               . modelToExprEnv $
                   s { curr_expr = CurrExpr Evaluate e'}

        (er, bindings') <- runG2WithSomes 
                    reducer
                    (SomeHalter SWHNFHalter)
                    (SomeOrderer NextOrderer)
                    solver simplifier emptyMemConfig s' bindings

        case er of
            [er'] -> do
                let (CurrExpr _ ce) = curr_expr . final_state $ er'
                return $ Just (bindings { name_gen = name_gen bindings' }, ce)
            [] -> return Nothing
            _ -> error $ "reduceAbstracted: Bad reduction"
    | otherwise = return $ Just (bindings, redVar (expr_env s) e) 

redVar :: E.ExprEnv -> Expr -> Expr
redVar = redVar' HS.empty

-- We use the hashset to track names we've seen, and make sure we don't loop forever on the same variable
redVar' :: HS.HashSet Name -> E.ExprEnv -> Expr -> Expr
redVar' rep eenv v@(Var (Id n t))
    | n `HS.member` rep = v
    | Just e <- E.lookup n eenv = redVar' (HS.insert n rep) eenv e
    -- We fill in fake LH dict variable for reduction, so they don't exist in the ExprEnv,
    -- but we don't want them to error
    | TyCon (Name tn _ _ _) _ <- t
    , tn == "lh" = v
    | otherwise = error $ "redVar: variable not found"
redVar' _ _ e = e

mapAccumM :: (Monad m, MonadPlus p) => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, p y)
mapAccumM _ z [] = return (z, mzero)
mapAccumM f z (x:xs) = do
  (z', y) <- f z x
  (z'', ys) <- mapAccumM f z' xs
  return (z'', return y `mplus` ys)

modelToExprEnv :: State t -> State t
modelToExprEnv s = s { expr_env = model s `E.union'` expr_env s
                     , model = HM.empty }

mkAssertsTrue :: ASTContainer t Expr => KnownValues -> State t -> State t
mkAssertsTrue kv = modifyASTs (mkAssertsTrue' (mkTrue kv))

mkAssertsTrue' :: Expr -> Expr -> Expr
mkAssertsTrue' tre (G2.Assert fc _ e) = G2.Assert fc tre e
mkAssertsTrue' _ e = e

elimSymGens :: ArbValueGen -> State t -> State t
elimSymGens arb s = s { expr_env = E.map esg $ expr_env s }
  where
    -- Rewriting the whole ExprEnv is slow, so we only
    -- rewrite an Expr if needed.
    esg e = 
        if hasSymGen e
            then modify (elimSymGens' (type_env s) arb) e
            else e

elimSymGens' :: TypeEnv -> ArbValueGen -> Expr -> Expr
elimSymGens' tenv arb (SymGen t) = fst $ arbValue t tenv arb
elimSymGens' _ _ e = e

hasSymGen :: Expr -> Bool
hasSymGen = getAny . eval hasSymGen'

hasSymGen' :: Expr -> Any
hasSymGen' (SymGen _) = Any True
hasSymGen' _ = Any False

-------------------------------
-- Generic
-------------------------------

pickHead :: (ASTContainer m Expr) => m -> m
pickHead = modifyASTs pickHead'

pickHead' :: Expr -> Expr
pickHead' (NonDet xs)
    | x:_ <- xs = x
    | otherwise = error "pickHead: empty NonDet"
pickHead' e = e