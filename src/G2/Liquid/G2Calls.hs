{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.G2Calls ( GathererReducer (..)
                         , checkAbstracted
                         , reduceAbstracted
                         , reduceAllCalls
                         , reduceCalls
                         , reduceFuncCall
                         , mapAccumM) where

import G2.Config
import G2.Data.Utils
import G2.Execution
import G2.Interface
import G2.Language as G2
import qualified G2.Language.ExprEnv as E
import G2.Liquid.Helpers
import G2.Liquid.LHReducers
import G2.Liquid.SpecialAsserts
import G2.Liquid.Types
import G2.Liquid.TyVarBags
import G2.Solver

import Control.Monad
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import Data.Tuple.Extra

import Data.Time.Clock

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
    let chck = checkAbstracted' solver simplifier (sharing config)
    ((s', bindings'), abstractedR) <- mapAccumM (uncurry chck) (s, bindings) (abstract_calls lht)
    let abstracted' = mapMaybe toAbstracted $ abstractedR
        models = mapMaybe toModel $ abstractedR

    -- Get an `Abstracted` for the initial call
    let init_call = FuncCall (idName init_id) inArg ex
    (s'', bindings'', abs_init, model_init) <- getAbstracted solver simplifier (sharing config) s' bindings' init_call

    -- Get an `Abstracted` for the violated function (if it exists)
    (bindings''', viol_er) <- reduceViolated solver simplifier (sharing config) bindings'' (er { final_state = s'' })
    abs_viol <- case violated viol_er of
                  Just v -> return . Just =<<
                              getAbstracted solver simplifier (sharing config) (final_state viol_er) bindings''' v
                  Nothing -> return Nothing
    let viol_model = maybeToList $ fmap fth4 abs_viol
        abs_info = AbstractedInfo { init_call = abs_init
                                  , abs_violated = fmap thd4 abs_viol
                                  , abs_calls = abstracted'
                                  , ai_all_calls = all_calls lht }
        fs = maybe (final_state viol_er) fst4 abs_viol
        fb = maybe bindings''' snd4 abs_viol

    return $ viol_er { final_state = fs { track = abs_info
                                        , model = foldr HM.union (model s) (model_init:viol_model ++ models) }
                     }

checkAbstracted' :: (Solver solver, Simplifier simplifier)
                 => solver
                 -> simplifier
                 -> Sharing
                 -> State LHTracker
                 -> Bindings
                 -> FuncCall
                 -> IO ((State LHTracker, Bindings), AbstractedRes)
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

        let pres = HS.fromList $ namesList s' ++ namesList bindings
        (er, bindings') <- runG2WithSomes 
                                (SomeReducer (StdRed share solver simplifier :<~ HitsLibError))
                                (SomeHalter (SWHNFHalter :<~> AcceptOnlyOneHalter :<~> SwitchEveryNHalter 200))
                                (SomeOrderer (ToOrderer $ IncrAfterN 2000 (ADTSizeOrderer 0 Nothing)))
                                solver simplifier
                                (emptyMemConfig { pres_func = \_ _ _ -> pres })
                                s' bindings

        case er of
            [ExecRes
                {
                    final_state = fs@(State { curr_expr = CurrExpr _ ce, model = m, track = t})
                }] -> case not $ ce `eqUpToTypes` r of
                        True -> do
                            let ar = AbstractRes 
                                        ( Abstracted { abstract = repTCsFC (type_classes s) $ abs_fc
                                                     , real = repTCsFC (type_classes s) $ abs_fc { returns = ce }
                                                     , hits_lib_err_in_real = t
                                                     , func_calls_in_real = [] }
                                        ) m
                            return ( ( s { expr_env = foldr E.insertSymbolic (expr_env s) (E.symbolicIds $ expr_env fs)
                                        , path_conds = path_conds fs }
                                     , bindings'
                                     )
                                   , ar)
                        False -> return ((s, bindings), NotAbstractRes)
            _ -> error $ "checkAbstracted': Bad return from runG2WithSomes"
    | otherwise = error $ "checkAbstracted': Bad lookup in runG2WithSomes"

getAbstracted :: (Solver solver, Simplifier simplifier)
              => solver
              -> simplifier
              -> Sharing 
              -> State LHTracker
              -> Bindings
              -> FuncCall
              -> IO (State LHTracker, Bindings, Abstracted, Model)
getAbstracted solver simplifier share s bindings abs_fc@(FuncCall { funcName = n, arguments = ars })
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

        let pres = HS.fromList $ namesList s' ++ namesList bindings
        (er, bindings') <- runG2WithSomes 
                              (SomeReducer (StdRed share solver simplifier :<~ HitsLibErrorGatherer))
                              (SomeHalter (SWHNFHalter :<~> AcceptOnlyOneHalter :<~> SwitchEveryNHalter 200))
                              (SomeOrderer (ToOrderer $ IncrAfterN 2000 (ADTSizeOrderer 0 Nothing)))
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
                  let ar = Abstracted { abstract = repTCsFC (type_classes s) abs_fc
                                      , real = repTCsFC (type_classes s) $ abs_fc { returns = (inline (expr_env fs) HS.empty ce) }
                                      , hits_lib_err_in_real = hle
                                      , func_calls_in_real = gfc' }
                  return ( s { expr_env = foldr E.insertSymbolic (expr_env s) (E.symbolicIds $ expr_env fs)
                             , path_conds = path_conds fs }
                         , bindings''
                         , ar
                         , m)
            _ -> error $ "checkAbstracted': Bad return from runG2WithSomes"
    | otherwise = error $ "getAbstracted: Bad lookup in runG2WithSomes" ++ show n

repTCsFC :: TypeClasses -> FuncCall -> FuncCall 
repTCsFC tc fc = fc { arguments = map (repTCs tc) (arguments fc)
                    , returns = repTCs tc (returns fc) }

repTCs :: TypeClasses -> Expr -> Expr
repTCs tc e
    | isTypeClass tc $ (typeOf e)
    , TyCon n _:t:_ <- unTyApp (typeOf e)
    , Just tc_dict <- typeClassInst tc M.empty n t = tc_dict
    | otherwise = e


inline :: ExprEnv -> HS.HashSet Name -> Expr -> Expr
inline h ns v@(Var (Id n _))
    | E.isSymbolic n h = v
    | HS.member n ns = v
    | Just e <- E.lookup n h = inline h (HS.insert n ns) e
inline h ns e = modifyChildren (inline h ns) e

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

data AcceptOnlyOneHalter = AcceptOnlyOneHalter

instance Halter AcceptOnlyOneHalter () t where
    initHalt _ _ = ()
    updatePerStateHalt _ hv _ _ = hv
    discardOnStart _ _ pr _ = not . null $ accepted pr
    stopRed _ _ _ _ = return Continue
    stepHalter _ hv _ _ _ = hv

-- | Remove all @Assume@s from the given `Expr`, unless they have a particular @Tick@
elimAssumesExcept :: ASTContainer m Expr => m -> m
elimAssumesExcept = modifyASTs elimAssumesExcept'

elimAssumesExcept' :: Expr -> Expr
elimAssumesExcept' (Assume _ (Tick t _) e)
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
    (bindings', er') <- reduceAbstracted solver simplifier (sharing config) bindings er
    (bindings'', er'') <- reduceAllCalls solver simplifier (sharing config) bindings' er'

    return (bindings'', er'')

reduceViolated :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> Sharing -> Bindings -> ExecRes LHTracker -> IO (Bindings, ExecRes LHTracker)
reduceViolated solver simplifier share bindings er@(ExecRes { final_state = s, violated = Just v }) = do
    let red = SomeReducer (StdRed share solver simplifier :<~| RedArbErrors)
    (s', bindings', v') <- reduceFuncCall red solver simplifier s bindings v
    -- putStrLn $ "v = " ++ show v
    -- putStrLn $ "v' = " ++ show v'
    return (bindings', er { final_state = s { expr_env = foldr E.insertSymbolic (expr_env s) (E.symbolicIds $ expr_env s')
                                            , path_conds = path_conds s' }
                          , violated = Just v' })
reduceViolated _ _ _ b er = return (b, er) 

reduceAbstracted :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> Sharing -> Bindings -> ExecRes LHTracker -> IO (Bindings, ExecRes LHTracker)
reduceAbstracted solver simplifier share bindings
                er@(ExecRes { final_state = (s@State { track = lht}) }) = do
    let red = SomeReducer (StdRed share solver simplifier :<~| RedArbErrors)
        fcs = abstract_calls lht

    ((s', bindings'), fcs') <- mapAccumM (\(s_, b_) fc -> do
                                            (new_s, new_b, r_fc) <- reduceFuncCall red solver simplifier s_ b_ fc
                                            return ((new_s, new_b), r_fc))
                            (s, bindings) fcs

    return (bindings', er { final_state = s { expr_env = foldr E.insertSymbolic (expr_env s) (E.symbolicIds $ expr_env s')
                                            , path_conds = path_conds s'
                                            , track = lht { abstract_calls = fcs' } }
                          })

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
                                  b_fc <- reduceFuncCallMaybe red solver simplifier s b fc
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
               => SomeReducer t -> solver -> simp -> State t -> Bindings -> FuncCall -> IO (State t, Bindings, FuncCall)
reduceFuncCall red solver simplifier s bindings fc@(FuncCall { arguments = ars, returns = r }) = do
    -- (bindings', red_ars) <- mapAccumM (reduceFCExpr share (red <~ SomeReducer (Logger "arg")) solver simplifier s) bindings ars
    -- (bindings'', red_r) <- reduceFCExpr share (red <~ SomeReducer (Logger "ret")) solver simplifier s bindings' r
    ((s', bindings'), red_ars) <- mapAccumM (uncurry (reduceFCExpr red solver simplifier)) (s, bindings) ars
    ((s'', bindings''), red_r) <- reduceFCExpr red solver simplifier s' bindings' r

    return (s'', bindings'', fc { arguments = red_ars, returns = red_r })

reduceFCExpr :: ( Solver solver
                , Simplifier simp
                , ASTContainer t Expr
                , ASTContainer t Type
                , Show t
                , Named t)
             => SomeReducer t -> solver -> simp -> State t -> Bindings -> Expr -> IO ((State t, Bindings), Expr)
reduceFCExpr reducer solver simplifier s bindings e 
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
                              (SomeHalter (AcceptOnlyOneHalter :<~> SWHNFHalter :<~> SwitchEveryNHalter 200))
                              (SomeOrderer (ToOrderer $ IncrAfterN 2000 (ADTSizeOrderer 0 Nothing)))
                              solver simplifier
                              emptyMemConfig
                              s' bindings

        case er of
            [er'] -> do
                let fs = final_state er'
                    (CurrExpr _ ce) = curr_expr fs
                return ((s' { expr_env = foldr E.insertSymbolic (expr_env s') (E.symbolicIds $ expr_env fs)
                            , path_conds = path_conds fs }
                        , bindings { name_gen = name_gen bindings' }), ce)
            _ -> error $ "reduceFCExpr: Bad reduction"
    | isTypeClass (type_classes s) $ (typeOf e)
    , TyCon n _:_ <- unTyApp (typeOf e)
    , _:Type t:_ <- unApp e
    , Just tc_dict <- typeClassInst (type_classes s) M.empty n t = 
          return $ ((s, bindings), tc_dict) 
    | otherwise = return ((s, bindings), redVar (expr_env s) e) 


reduceFuncCallMaybe :: ( Solver solver
                       , Simplifier simp
                       , ASTContainer t Expr
                       , ASTContainer t Type
                       , Show t
                       , Named t)
                    => SomeReducer t -> solver -> simp -> State t -> Bindings -> FuncCall -> IO (Maybe (Bindings, FuncCall))
reduceFuncCallMaybe red solver simplifier s bindings fc@(FuncCall { arguments = ars, returns = r }) = do
    ((_, bindings'), red_ars)  <- mapAccumM (uncurry (reduceFCExpr red solver simplifier)) (s, bindings) ars
    ((_, bindings''), red_r) <- reduceFCExpr red solver simplifier s bindings' r

    return $ Just (bindings'', fc { arguments = red_ars, returns = red_r })

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
modelToExprEnv s =
    let
         m = HM.filterWithKey (\k _ -> k /= idName existentialInstId && k /= idName postSeqExistentialInstId) (model s)
    in
    s { expr_env = m `E.union'` expr_env s
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