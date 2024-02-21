{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}

{-| Module: G2.Execution.Reducer

Controls reduction of `State`s.

The `runReducer` function reduces States, guided by a `Reducer`, `Halter`, and `Orderer`.
The `Reducer` defines the reduction rules used to map a State to one or more further States.
The `Halter` determines when to accept (return) or completely discard a state,
and allows /temporarily/ stopping reduction of a particular state, to allow reduction of other states.
The `Orderer` determines which state should be executed next when the Halter chooses to accept, reject,
or switch to executing a different state.
-}
module G2.Execution.Reducer ( Reducer (..)

                            , Halter (..)
                            , InitHalter
                            , UpdatePerStateHalt
                            , StopRed
                            , StepHalter

                            , Orderer (..)
                            , InitOrderer
                            , OrderStates
                            , UpdateSelected

                            , Processed (..)
                            , mapProcessed

                            , ReducerRes (..)
                            , HaltC (..)

                            , SomeReducer (..)
                            , SomeHalter (..)
                            , SomeOrderer (..)

                            -- * Reducers
                            , InitReducer
                            , RedRules
                            , mkSimpleReducer
                            , stdRed
                            , nonRedPCTemplates
                            , nonRedLibFuncsReducer
                            , nonRedPCRed
                            , nonRedPCRedConst
                            , taggerRed
                            , getLogger
                            , simpleLogger
                            , prettyLogger
                            , limLogger
                            , LimLogger (..)

                            , ReducerEq (..)
                            , (.==)
                            , (~>)
                            , (.~>)
                            , (-->)
                            , (.-->)

                            , (.|.)

                            -- * Halters
                            , mkSimpleHalter
                            , swhnfHalter
                            , acceptIfViolatedHalter
                            , (<~>)
                            , zeroHalter
                            , discardIfAcceptedTagHalter
                            , maxOutputsHalter
                            , switchEveryNHalter
                            , varLookupLimitHalter
                            , stdTimerHalter
                            , timerHalter

                            -- * Orderers
                            , mkSimpleOrderer
                            , (<->)
                            , ordComb
                            , nextOrderer
                            , pickLeastUsedOrderer
                            , bucketSizeOrderer
                            , adtHeightOrderer
                            , adtSizeOrderer
                            , pcSizeOrderer
                            , incrAfterN
                            , quotTrueAssert

                            -- * Execution
                            , runReducer ) where

import G2.Config
import qualified G2.Language.ExprEnv as E
import G2.Execution.Rules
import G2.Language
import qualified G2.Language.Monad as MD
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as Stck
import G2.Solver
import G2.Lib.Printers

import Control.Monad.IO.Class
import qualified Control.Monad.State as SM
import Data.Foldable
import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid ((<>))
import qualified Data.List as L
import qualified Data.Text as T
import Data.Tuple
import Data.Time.Clock
import System.Directory
import Debug.Trace

-- | Used when applying execution rules
-- Allows tracking extra information to control halting of rule application,
-- and to reorder states
-- see also, the Reducer, Halter, Orderer typeclasses
-- cases is used for logging states
data ExState rv hv sov t = ExState { state :: State t
                                   , reducer_val :: rv
                                   , halter_val :: hv
                                   , order_val :: sov
                                   }

-- | Keeps track of type a's that have either been accepted or dropped
data Processed a = Processed { accepted :: [a]
                             , discarded :: [a] }

mapProcessed :: (a -> b) -> Processed a -> Processed b
mapProcessed f pr = Processed { accepted = map f (accepted pr)
                              , discarded = map f (discarded pr)}

-- | Used by Reducers to indicate their progress reducing.
data ReducerRes = NoProgress | InProgress | Finished deriving (Eq, Ord, Show, Read)

progPrioritizer :: ReducerRes -> ReducerRes -> ReducerRes
progPrioritizer InProgress _ = InProgress
progPrioritizer _ InProgress = InProgress
progPrioritizer Finished _ = Finished
progPrioritizer _ Finished = Finished
progPrioritizer _ _ = NoProgress

-- | Used by members of the Halter typeclass to control whether to continue
-- evaluating the current State, or switch to evaluating a new state.
data HaltC = Discard -- ^ Switch to evaluating a new state, and reject the current state
           | Accept -- ^ Switch to evaluating a new state, and accept the current state
           | Switch -- ^ Switch to evaluating a new state, but continue evaluating the current state later
           | Continue -- ^ Continue evaluating the current State
           deriving (Eq, Ord, Show, Read)

type InitReducer rv t = State t -> rv
type RedRules m rv t = rv -> State t -> Bindings -> m (ReducerRes, [(State t, rv)], Bindings)


-- | A Reducer is used to define a set of Reduction Rules.
-- Reduction Rules take a `State`, and output new `State`s.
-- The reducer value, rv, can be used to track extra information, on a per `State` basis.
data Reducer m rv t = Reducer {
        -- | Initialized the reducer value
          initReducer :: InitReducer rv t

        -- | Takes a State, and performs the appropriate Reduction Rule
        , redRules :: RedRules m rv t

        -- | After a reducer returns multiple states,
        -- gives an opportunity to update with all States and Reducer values's,
        -- visible.
        -- Errors if the returned list is too short.
        -- If only one state is returned by all reducers, updateWithAll does not run.
        , updateWithAll :: [(State t, rv)] -> [rv]

        , onAccept :: State t -> rv -> m ()
    }

-- | A simple, default reducer.
-- `updateWithAll` does not change or adjust the reducer values.
-- `onAccept` immediately returns the empty tuple.
mkSimpleReducer :: Monad m => InitReducer rv t -> RedRules m rv t -> Reducer m rv t
mkSimpleReducer init_red red_rules =
    Reducer {
      initReducer = init_red
    , redRules = red_rules
    , updateWithAll = map snd
    , onAccept = \_ _ -> return ()
    }
{-# INLINE mkSimpleReducer #-}

type InitHalter hv t = State t -> hv
type UpdatePerStateHalt hv t = hv -> Processed (State t) -> State t -> hv
type StopRed m hv t = hv -> Processed (State t) -> State t -> m HaltC
type StepHalter hv t = hv -> Processed (State t) -> [State t] -> State t -> hv

-- | Determines when to stop evaluating a state
-- The halter value, hv, can be used to track extra information, on a per `State` basis.
data Halter m hv t = Halter {
    -- | Initializes each state halter value
      initHalt :: InitHalter hv t

    -- | Runs whenever we switch to evaluating a different state,
    -- to update the halter value of that new state
    , updatePerStateHalt :: UpdatePerStateHalt hv t

    -- | Runs when we start execution on a state, immediately after
    -- `updatePerStateHalt`.  Allows a State to be discarded right
    -- before execution is about to (re-)begin.
    -- Return True if execution should proceed, False to discard
    , discardOnStart :: hv -> Processed (State t) -> State t -> Bool

    -- | Determines whether to continue reduction on the current state
    , stopRed :: StopRed m hv t

    -- | Takes a state, and updates its halter record field
    , stepHalter :: StepHalter hv t

    -- | After multiple states, are returned
    -- gives an opportunity to update halters with all States and halter values visible.
    -- Errors if the returned list is too short.
    -- If only one state is returned, updateHalterWithAll does not run.
    , updateHalterWithAll :: [(State t, hv)] -> [hv]
    }

-- | A simple, default halter.
mkSimpleHalter :: Monad m => InitHalter hv t -> UpdatePerStateHalt hv t -> StopRed m hv t -> StepHalter hv t -> Halter m hv t
mkSimpleHalter initial update stop step = Halter { initHalt = initial
                                                 , updatePerStateHalt = update
                                                 , discardOnStart = \_ _ _ -> False
                                                 , stopRed = stop
                                                 , stepHalter = step
                                                 , updateHalterWithAll = map snd }
{-# INLINE mkSimpleHalter #-}

{-# INLINE mkStoppingHalter #-}
mkStoppingHalter :: Monad m => StopRed m () t -> Halter m () t
mkStoppingHalter stop =
            mkSimpleHalter
                (const ())
                (\_ _ _ -> ())
                stop
                (\_ _ _ _ -> ())


type InitOrderer sov t = State t -> sov
type OrderStates sov b t = sov -> Processed (State t) -> State t -> b
type UpdateSelected sov t = sov -> Processed (State t) -> State t -> sov

-- | Picks an order to evaluate the states, to allow prioritizing some over others.
-- The orderer value, sov, can be used to track extra information, on a per `State` basis.
-- The ordering type b, is used to determine what order to execute the states in.
-- In practice, `b` must be an instance of `Ord`.  When the orderer is called, the `State` corresponding
-- to the minimal `b` is executed.
data Orderer sov b t = Orderer {
    -- | Initializing the per state ordering value 
      initPerStateOrder :: InitOrderer sov t

    -- | Assigns each state some value of an ordered type, and then proceeds with execution on the
    -- state assigned the minimal value
    , orderStates :: OrderStates sov b t

    -- | Run on the selected state, to update it's sov field
    , updateSelected :: UpdateSelected sov t

    -- | Run on the state at each step, to update it's sov field
    , stepOrderer :: sov -> Processed (State t) -> [State t] -> State t -> sov
    }

-- | A simple, default orderer.
mkSimpleOrderer :: InitOrderer sov t -> OrderStates sov b t -> UpdateSelected sov t -> Orderer sov b t
mkSimpleOrderer initial order update = Orderer { initPerStateOrder = initial
                                               , orderStates = order
                                               , updateSelected = update
                                               , stepOrderer = \sov _ _ _ -> sov}

getState :: M.Map b [s] -> Maybe (b, [s])
getState = M.lookupMin

-- | Hide the details of a Reducer's reducer value.
data SomeReducer m t where
    SomeReducer :: forall m rv t . Reducer m rv t -> SomeReducer m t

-- | Hide the details of a Halter's halter value.
data SomeHalter m t where
    SomeHalter :: forall m hv t . Halter m hv t -> SomeHalter m t

-- | Hide the details of an Orderer's orderer value and ordering type.
data SomeOrderer t where
    SomeOrderer :: forall sov b t . Ord b => Orderer sov b t -> SomeOrderer t


-- Combines multiple reducers together into a single reducer.

-- We use RC to combine the reducer values for RCombiner
-- We should never define any other instance of Reducer with RC, or export it
-- because this could lead to undecidable instances
data RC a b = RC a b

-- | Check if a `Reducer` returns some specific `ReducerRes`
data ReducerEq m t where
    (:==) :: forall m rv t . Reducer m rv t -> ReducerRes -> ReducerEq m t

(.==) :: SomeReducer m t -> ReducerRes -> ReducerEq m t
SomeReducer r .== res = r :== res

infixr 8 .==

infixr 7 ~>, .~>

infixr 5 -->, .-->

-- | @r1 ~> r2@ applies `Reducer` `r1`, followed by reducer `r2`. 
(~>) :: Monad m => Reducer m rv1 t -> Reducer m rv2 t -> Reducer m (RC rv1 rv2) t
r1 ~> r2 =
    Reducer { initReducer = \s -> RC (initReducer r1 s) (initReducer r2 s)

            , redRules = \(RC rv1 rv2) s b -> do
                (rr1, srv1, b') <- redRules r1 rv1 s b
                (rr2, srv2, b'') <- redRulesToStates r2 rv2 srv1 b'

                return (progPrioritizer rr1 rr2, srv2, b'')

            , updateWithAll = updateWithAllPair (updateWithAll r1) (updateWithAll r2)

            , onAccept = \s (RC rv1 rv2) -> do
                onAccept r1 s rv1
                onAccept r2 s rv2
            }
{-# INLINE (~>) #-}

-- | `~>` adjusted to work on `SomeReducer`s, rather than `Reducer`s.
(.~>) :: Monad m => SomeReducer m t -> SomeReducer m t -> SomeReducer m t
SomeReducer r1 .~> SomeReducer r2 = SomeReducer (r1 ~> r2)
{-# INLINE (.~>) #-}

-- | @r1 := res --> r2@ applies `Reducer` `r1`.  If `r1` returns the `ReducerRes` `res`,
-- then `Reducer` `r2` is applied.  Otherwise, reduction halts.  
(-->) :: Monad m => ReducerEq m t -> Reducer m rv2 t -> SomeReducer m t
(r1 :== res) --> r2 =
    SomeReducer $
        Reducer { initReducer = \s -> RC (initReducer r1 s) (initReducer r2 s)

                , redRules = \(RC rv1 rv2) s b -> do
                    (rr1, srv1, b') <- redRules r1 rv1 s b
                    let (s', rv1') = unzip srv1

                    case rr1 == res of
                        True -> do
                            (rr2, ss, b'') <- redRulesToStates r2 rv2 srv1 b'
                            return (rr2, ss, b'')
                        False -> return (rr1, zip s' (map (flip RC rv2) rv1'), b')

                , updateWithAll = updateWithAllPair (updateWithAll r1) (updateWithAll r2)

                , onAccept = \s (RC rv1 rv2) -> do
                    onAccept r1 s rv1
                    onAccept r2 s rv2
                }
{-# INLINE (-->) #-}

-- | `.-->` adjusted to take a `SomeReducer`, rather than a `Reducer`s.
(.-->) :: Monad m => ReducerEq m t -> SomeReducer m t -> SomeReducer m t
req .--> SomeReducer r = req --> r

redRulesToStatesAux :: Monad m =>  Reducer m rv2 t -> rv2 -> Bindings -> (State t, rv1) -> m (Bindings, (ReducerRes, [(State t, RC rv1 rv2)]))
redRulesToStatesAux r rv2 b (is, rv1) = do
        (rr_, is', b') <- redRules r rv2 is b
        return (b', (rr_, map (\(is'', rv2') -> (is'', RC rv1 rv2') ) is'))

redRulesToStates :: Monad m => Reducer m rv2 t -> rv2 -> [(State t, rv1)] -> Bindings -> m (ReducerRes, [(State t, RC rv1 rv2)], Bindings)
redRulesToStates r rv1 s b = do
    let redRulesToStatesAux' = redRulesToStatesAux r rv1
    (b', rs) <- MD.mapMAccumB redRulesToStatesAux' b s

    let (rr, s') = L.unzip rs

    let rf = foldr progPrioritizer NoProgress rr

    return $ (rf, concat s', b')

-- | @r1 .|. r2@ applies both Reducer r1 and Reducer r2 to the \inital\ state passed to the reducer,
-- and returns the list of states returned from both reducers combined.
-- Care should be taken to avoid unwanted duplication of states if, for example, neither of the reducers
-- makes progress.
(.|.) :: Monad m => Reducer m rv1 t -> Reducer m rv2 t -> Reducer m (RC rv1 rv2) t
r1 .|. r2 =
    Reducer { initReducer = \s -> RC (initReducer r1 s) (initReducer r2 s)

            , redRules = \(RC rv1 rv2) s b -> do
                (rr2, srv2, b') <- redRules r2 rv2 s b
                (rr1, srv1, b'') <- redRules r1 rv1 s b'

                let srv2' = map (\(s_, rv2_) -> (s_, RC rv1 rv2_) ) srv2
                    srv1' = map (\(s_, rv1_) -> (s_, RC rv1_ rv2) ) srv1

                return (progPrioritizer rr1 rr2, srv2' ++ srv1', b'')

            , updateWithAll = updateWithAllPair (updateWithAll r1) (updateWithAll r2)

            , onAccept = \s (RC rv1 rv2) -> do
                onAccept r1 s rv1
                onAccept r2 s rv2
            }
{-# INLINE (.|.) #-}

updateWithAllPair :: ([(State t, rv1)] -> [rv1]) -> ([(State t, rv2)] -> [rv2]) -> [(State t, RC rv1 rv2)] -> [RC rv1 rv2]
updateWithAllPair update1 update2 srv =
                let
                    srv1 = map (\(s, RC rv1 _) -> (s, rv1)) srv
                    srv2 = map (\(s, RC _ rv2) -> (s, rv2)) srv

                    rv1' = update1 srv1
                    rv2' = update2 srv2
                in
                map (uncurry RC) $ zip rv1' rv2'

{-#INLINE stdRed #-}
{-# SPECIALIZE stdRed :: (Solver solver, Simplifier simplifier) => Sharing -> SymbolicFuncEval t -> solver -> simplifier -> Reducer IO () t #-}
stdRed :: (MonadIO m, Solver solver, Simplifier simplifier) => Sharing -> SymbolicFuncEval t -> solver -> simplifier -> Reducer m () t
stdRed share symb_func_eval solver simplifier =
        mkSimpleReducer (\_ -> ())
                        (\_ s b -> do
                            (r, s', b') <- liftIO $ stdReduce share symb_func_eval solver simplifier s b

                            return (if r == RuleIdentity then Finished else InProgress, s', b')
                        )

-- | Pushes non_red_path_conds onto the exec_stack for solving higher order symbolic function 
nonRedPCTemplates :: Monad m => Reducer m () t
nonRedPCTemplates = mkSimpleReducer (\_ -> ())
                        nonRedPCTemplatesFunc

nonRedPCTemplatesFunc :: Monad m => RedRules m () t
nonRedPCTemplatesFunc _
                      s@(State { expr_env = eenv
                         , curr_expr = cexpr
                         , exec_stack = stck
                         , non_red_path_conds = (nre1, nre2):nrs
                         , model = m })
                        b@(Bindings { name_gen = ng }) =
    
    let
        stck' = Stck.push (CurrExprFrame (EnsureEq nre2) cexpr) stck
        s' = s { exec_stack = stck', non_red_path_conds = nrs }
    in
    case retReplaceSymbFuncTemplate s' ng nre1 of
        Just (r, s'', ng') -> return (InProgress, zip s'' (repeat ()), b {name_gen = ng'})
        Nothing ->
            let 
                s'' = s' {curr_expr = CurrExpr Evaluate nre1}
            in return (InProgress, [(s'', ())], b)
nonRedPCTemplatesFunc _ s b = return (Finished, [(s, ())], b)

nonRedLibFuncsReducer :: Monad m => HS.HashSet Name -> Reducer m () t
nonRedLibFuncsReducer n = mkSimpleReducer (\_ -> ())
                            (nonRedLibFuncs n)

nonRedLibFuncs :: Monad m => HS.HashSet Name -> RedRules m () t
nonRedLibFuncs names _ s@(State { expr_env = eenv
                         , curr_expr = CurrExpr _ ce
                         , non_red_path_conds = nrs
                         }) 
                         b@(Bindings { name_gen = ng })
    | Var (Id n t):es <- unApp ce
    , hasFuncType (PresType t)
    , not (hasFuncType ce) = 
        let
            isMember =  HS.member n names
        in
            case isMember of
                True -> let
                            (new_sym, ng') = freshSeededName n ng
                            new_sym_id = Id new_sym (typeOf ce)
                            eenv' = E.insertSymbolic new_sym_id eenv
                            cexpr' = CurrExpr Return (Var new_sym_id)
                            -- nonRedBlocker is just a tick name to avoid reducing function and adding to non-reduced path constraint
                            nonRedBlocker = Name "NonRedBlocker" Nothing 0 Nothing
                            tick = NamedLoc nonRedBlocker
                            ce' = mkApp $ (Tick tick (Var (Id n t))):es
                            s' = s { expr_env = eenv',
                                    curr_expr = cexpr',
                                    non_red_path_conds = nrs ++ [(ce', Var new_sym_id)] } 
                        in 
                            return (Finished, [(s', ())], b {name_gen = ng'})
                False -> return (Finished, [(s, ())], b)

    | otherwise = return (Finished, [(s, ())], b)
     


-- | Removes and reduces the values in a State's non_red_path_conds field. 
{-#INLINE nonRedPCRed #-}
nonRedPCRed :: Monad m => Reducer m () t
nonRedPCRed = mkSimpleReducer (\_ -> ())
                              nonRedPCRedFunc

nonRedPCRedFunc :: Monad m => RedRules m () t
nonRedPCRedFunc _
                s@(State { expr_env = eenv
                         , curr_expr = cexpr
                         , exec_stack = stck
                         , non_red_path_conds = (nre1, nre2):nrs
                         , model = m })
                b@(Bindings { higher_order_inst = inst })
    | Var (Id n t) <- nre2
    , E.isSymbolic n eenv
    , hasFuncType (PresType t) =
        let
            s' = s { expr_env = E.insert n nre1 eenv
                   , non_red_path_conds  = nrs }
        in
        return (InProgress, [(s', ())], b)
    | Var (Id n t) <- nre1
    , E.isSymbolic n eenv
    , hasFuncType (PresType t) =
        let
            s' = s { expr_env = E.insert n nre2 eenv
                   , non_red_path_conds  = nrs }
        in
        return (InProgress, [(s', ())], b)
    | otherwise = do
        let stck' = Stck.push (CurrExprFrame (EnsureEq nre2) cexpr) stck

        let cexpr' = CurrExpr Evaluate nre1

        let eenv_si_ces = substHigherOrder eenv m inst cexpr'

        let s' = s { exec_stack = stck'
                   , non_red_path_conds = nrs
                   }
            xs = map (\(eenv', m', ce) -> (s' { expr_env = eenv'
                                              , model = m'
                                              , curr_expr = ce }, ())) eenv_si_ces

        return (InProgress, xs, b)
nonRedPCRedFunc _ s b = return (Finished, [(s, ())], b)

-- [Higher-Order Model]
-- Substitutes all possible higher order functions for symbolic higher order functions.
-- We insert the substituted higher order function directly into the model, because, due
-- to the VAR-RED rule, the function name will (if the function is called) be lost during execution.
substHigherOrder :: ExprEnv -> Model -> HS.HashSet Name -> CurrExpr -> [(ExprEnv, Model, CurrExpr)]
substHigherOrder eenv m ns ce =
    let
        is = mapMaybe (\n -> case E.lookup n eenv of
                                Just e -> Just $ Id n (typeOf e)
                                Nothing -> Nothing) $ HS.toList ns

        higherOrd = filter (isTyFun . typeOf) . symbVars eenv $ ce
        higherOrdSub = map (\v -> (v, mapMaybe (genSubstitutable v) is)) higherOrd
    in
    substHigherOrder' [(eenv, m, ce)] higherOrdSub
    where
        genSubstitutable v i
            | Just bm <- specializes (typeOf v) (typeOf i) =
                let
                    bnds = map idName $ leadingTyForAllBindings i
                    tys = mapMaybe (\b -> fmap Type $ M.lookup b bm) bnds
                in
                Just . mkApp $ Var i:tys
            | otherwise = Nothing

substHigherOrder' :: [(ExprEnv, Model, CurrExpr)] -> [(Id, [Expr])] -> [(ExprEnv, Model, CurrExpr)]
substHigherOrder' eenvsice [] = eenvsice
substHigherOrder' eenvsice ((i, es):iss) =
    substHigherOrder'
        (concatMap (\e_rep ->
                        map (\(eenv, m, ce) -> ( E.insert (idName i) e_rep eenv
                                               , HM.insert (idName i) e_rep m
                                               , replaceASTs (Var i) e_rep ce)
                            ) eenvsice)
        es) iss

-- | Removes and reduces the values in a State's non_red_path_conds field
-- by instantiating higher order functions to be constant.
-- Does not return any states if the state does not contain at least one
-- higher order symbolic variable.
nonRedPCRedConst :: Monad m => Reducer m () t
nonRedPCRedConst = mkSimpleReducer (\_ -> ())
                                   nonRedPCRedConstFunc

nonRedPCRedConstFunc :: Monad m => RedRules m () t
nonRedPCRedConstFunc _
                     s@(State { expr_env = eenv
                              , curr_expr = cexpr
                              , exec_stack = stck
                              , non_red_path_conds = (nre1, nre2):nrs
                              , model = m })
                     b@(Bindings { name_gen = ng })
    | higher_ord <- L.filter (isTyFun . typeOf) $ E.symbolicIds eenv
    , not (null higher_ord) = do
        let stck' = Stck.push (CurrExprFrame (EnsureEq nre2) cexpr) stck

        let cexpr' = CurrExpr Evaluate nre1

        let (ng', new_lam_is) = L.mapAccumL (\ng_ ts -> swap $ freshIds ts ng_) ng (map anonArgumentTypes higher_ord)
            (new_sym_gen, ng'') = freshIds (map returnType higher_ord) ng'

            es = map (\(f_id, lam_i, sg_i) -> (f_id, mkLams (zip (repeat TermL) lam_i) (Var sg_i)) )
               $ zip3 higher_ord new_lam_is new_sym_gen

            eenv' = foldr (uncurry E.insert) eenv (map (\(i, e) -> (idName i, e)) es)
            eenv'' = foldr E.insertSymbolic eenv' new_sym_gen
            m' = foldr (\(i, e) -> HM.insert (idName i) e) m es

        let s' = s { expr_env = eenv''
                , curr_expr = cexpr'
                , model = m'
                , exec_stack = stck'
                , non_red_path_conds = nrs
                }

        return (InProgress, [(s', ())], b { name_gen = ng'' })
nonRedPCRedConstFunc _ s b = return (Finished, [], b)

{-# INLINE taggerRed #-}
taggerRed :: Monad m => Name -> Reducer m () t
taggerRed n = mkSimpleReducer (const ()) (taggerRedStep n)

taggerRedStep :: Monad m => Name -> RedRules m () t
taggerRedStep n _ s@(State {tags = ts}) b@(Bindings { name_gen = ng }) =
    let
        (n'@(Name n_ m_ _ _), ng') = freshSeededName n ng
    in
    if null $ HS.filter (\(Name n__ m__ _ _) -> n_ == n__ && m_ == m__) ts then
        return (Finished, [(s {tags = HS.insert n' ts}, ())], b { name_gen = ng' })
    else
        return (Finished, [(s, ())], b)


getLogger :: (MonadIO m, Show t) => Config -> Maybe (Reducer (SM.StateT PrettyGuide m) [Int] t)
getLogger config = case logStates config of
                        Log Raw fp -> Just (simpleLogger fp)
                        Log Pretty fp -> Just (prettyLogger fp)
                        NoLog -> Nothing

-- | A Reducer to producer logging output 
simpleLogger :: (MonadIO m, Show t) => FilePath -> Reducer m [Int] t
simpleLogger fn =
    (mkSimpleReducer (const [])
                     (\li s b -> do
                        liftIO $ outputState fn li s b pprExecStateStr
                        return (NoProgress, [(s, li)], b) ))
                    { updateWithAll = \s -> map (\(l, i) -> l ++ [i]) $ zip (map snd s) [1..] }

-- | A Reducer to producer logging output 
prettyLogger :: (MonadIO m, Show t) => FilePath -> Reducer (SM.StateT PrettyGuide m) [Int] t
prettyLogger fp =
    (mkSimpleReducer
        (const [])
        (\li s b -> do
            pg <- SM.get
            let pg' = updatePrettyGuide (s { track = () }) pg
            SM.put pg'
            liftIO $ outputState fp li s b (\s_ _ -> T.unpack $ prettyState pg' s_)
            return (NoProgress, [(s, li)], b)
        )
    ) { updateWithAll = \s -> map (\(l, i) -> l ++ [i]) $ zip (map snd s) [1..]
      , onAccept = \_ ll -> liftIO . putStrLn $ "Accepted on path " ++ show ll }

-- | A Reducer to producer limited logging output.
data LimLogger =
    LimLogger { every_n :: Int -- Output a state every n steps
              , after_n :: Int -- Only begin outputting after passing a certain n
              , before_n :: Maybe Int -- Only output before a certain n
              , down_path :: [Int] -- Output states that have gone down or are going down the given path prefix
              , lim_output_path :: String
              }

data LLTracker = LLTracker { ll_count :: Int, ll_offset :: [Int]}

limLogger :: (MonadIO m, Show t) => LimLogger -> Reducer m LLTracker t
limLogger ll@(LimLogger { after_n = aft, before_n = bfr, down_path = down }) =
    (mkSimpleReducer (const $ LLTracker { ll_count = every_n ll, ll_offset = []}) rr)
        { updateWithAll = updateWithAllLL
        , onAccept = \_ llt -> liftIO . putStrLn $ "Accepted on path " ++ show (ll_offset llt)}
    where
        rr llt@(LLTracker { ll_count = 0, ll_offset = off }) s b
            | down `L.isPrefixOf` off || off `L.isPrefixOf` down
            , aft <= length_rules && maybe True (length_rules <=) bfr = do
                liftIO $ outputState (lim_output_path ll) off s b pprExecStateStr
                return (NoProgress, [(s, llt { ll_count = every_n ll })], b)
            | otherwise =
                return (NoProgress, [(s, llt { ll_count = every_n ll })], b)
            where
                length_rules = length (rules s)
        rr llt@(LLTracker {ll_count = n}) s b =
            return (NoProgress, [(s, llt { ll_count = n - 1 })], b)

        updateWithAllLL [(_, l)] = [l]
        updateWithAllLL ss =
            map (\(llt, i) -> llt { ll_offset = ll_offset llt ++ [i] }) $ zip (map snd ss) [1..]

outputState :: FilePath -> [Int] -> State t -> Bindings -> (State t -> Bindings -> String) -> IO ()
outputState dn is s b printer = do
    fn <- getFile dn is "state" s

    -- Don't re-output states that  already exist
    exists <- doesPathExist fn

    if not exists
        then do
            let write = printer s b
            writeFile fn write

            putStrLn fn
        else return ()

getFile :: String -> [Int] -> String -> State t -> IO String
getFile dn is n s = do
    let dir = dn ++ "/" ++ foldl' (\str i -> str ++ show i ++ "/") "" is
    createDirectoryIfMissing True dir
    let fn = dir ++ n ++ show (length $ rules s) ++ ".txt"
    return fn

-- We use C to combine the halter values for HCombiner
-- We should never define any other instance of Halter with C, or export it
-- because this could lead to undecidable instances
data C a b = C a b deriving Eq

instance (ASTContainer a Expr, ASTContainer b Expr) => ASTContainer (C a b) Expr where
    containedASTs (C a b) = containedASTs a ++ containedASTs b
    modifyContainedASTs f (C a b) = C (modifyContainedASTs f a) (modifyContainedASTs f b)

instance (ASTContainer a Type, ASTContainer b Type) => ASTContainer (C a b) Type where
    containedASTs (C a b) = containedASTs a ++ containedASTs b
    modifyContainedASTs f (C a b) = C (modifyContainedASTs f a) (modifyContainedASTs f b)

instance (Named a, Named b) => Named (C a b) where
    names (C a b) = names a <> names b
    rename old new (C a b) = C (rename old new a) (rename old new b)
    renames hm (C a b) = C (renames hm a) (renames hm b)

-- | Allows executing multiple halters.
-- If the halters disagree, prioritizes the order:
-- Discard, Accept, Switch, Continue
(<~>) :: Monad m => Halter m hv1 t -> Halter m hv2 t -> Halter m (C hv1 hv2) t
h1 <~> h2 =
    Halter {
              initHalt = \s ->
                let
                    hv1 = initHalt h1 s
                    hv2 = initHalt h2 s
                in
                C hv1 hv2

            , updatePerStateHalt = \(C hv1 hv2) proc s ->
                let
                    hv1' = updatePerStateHalt h1 hv1 proc s
                    hv2' = updatePerStateHalt h2 hv2 proc s
                in
                C hv1' hv2'

            , discardOnStart = \(C hv1 hv2) proc s ->
                let
                    b1 = discardOnStart h1 hv1 proc s
                    b2 = discardOnStart h2 hv2 proc s
                in
                b1 || b2

            , stopRed = \(C hv1 hv2) proc s -> do
                hc1 <- stopRed h1 hv1 proc s
                hc2 <- stopRed h2 hv2 proc s

                return $ min hc1 hc2

            , stepHalter = \(C hv1 hv2) proc xs s ->
                let
                    hv1' = stepHalter h1 hv1 proc xs s
                    hv2' = stepHalter h2 hv2 proc xs s
                in
                C hv1' hv2'

            , updateHalterWithAll = \shv ->
                let
                    shv1 = map (\(s, C hv1 _) -> (s, hv1)) shv
                    shv2 = map (\(s, C _ hv2) -> (s, hv2)) shv

                    shv1' = updateHalterWithAll h1 shv1
                    shv2' = updateHalterWithAll h2 shv2
                in
                map (uncurry C) $ zip shv1' shv2'
            }
{-# INLINE (<~>) #-}

{-# INLINE swhnfHalter #-}
swhnfHalter :: Monad m => Halter m () t
swhnfHalter = mkStoppingHalter stop
    where
        stop _ _ s =
            case isExecValueForm s of
                True -> return Accept
                False -> return Continue

-- | Accepts a state when it is in SWHNF and true_assert is true
-- Discards it if in SWHNF and true_assert is false
acceptIfViolatedHalter :: Monad m => Halter m () t
acceptIfViolatedHalter = mkStoppingHalter stop
    where
        stop _ _ s =
            case isExecValueForm s of
                True
                    | true_assert s -> return Accept
                    | otherwise -> return Discard
                False -> return Continue

-- | Allows execution to continue until the step counter hits 0, then discards the state
zeroHalter :: Monad m => Int -> Halter m Int t
zeroHalter n = mkSimpleHalter
                    (const n)
                    (\h _ _ -> h)
                    (\h _ _ -> if h == 0 then return Discard else return Continue)
                    (\h _ _ _ -> h - 1)

maxOutputsHalter :: Monad m => Maybe Int -> Halter m (Maybe Int) t
maxOutputsHalter m = mkSimpleHalter
                        (const m)
                        (\hv _ _ -> hv)
                        (\_ (Processed {accepted = acc}) _ ->
                            case m of
                                Just m' -> return $ if length acc >= m' then Discard else Continue
                                _ -> return Continue)
                        (\hv _ _ _ -> hv)

-- | Switch execution every n steps
{-# INLINE switchEveryNHalter #-}
switchEveryNHalter :: Monad m => Int -> Halter m Int t
switchEveryNHalter sw = (mkSimpleHalter
                            (const sw)
                            (\_ _ _ -> sw)
                            (\i _ _ -> return $ if i <= 0 then Switch else Continue)
                            (\i _ _ _ -> i - 1))
                        { updateHalterWithAll = updateAll }
    where
        updateAll [] = []
        updateAll xs@((_, c):_) =
            let
                len = length xs
                c' = c `quot` len
            in
            replicate len c'

-- | If the Name, disregarding the Unique, in the DiscardIfAcceptedTag
-- matches a Tag in the Accepted State list,
-- and in the State being evaluated, discard the State
discardIfAcceptedTagHalter :: Monad m => Name -> Halter m (HS.HashSet Name) t
discardIfAcceptedTagHalter (Name n m _ _) =
                            mkSimpleHalter
                                (const HS.empty)
                                ups
                                (\ns _ _ -> return $ if not (HS.null ns) then Discard else Continue)
                                (\hv _ _ _ -> hv)
    where
        ups _
            (Processed {accepted = acc})
            (State {tags = ts}) =
                let
                    allAccTags = HS.unions $ map tags acc
                    matchCurrState = HS.intersection ts allAccTags
                in
                HS.filter (\(Name n' m' _ _) -> n == n' && m == m') matchCurrState

-- | Counts the number of variable lookups are made, and switches the state
-- whenever we've hit a threshold
varLookupLimitHalter :: Monad m => Int -> Halter m Int t
varLookupLimitHalter lim = mkSimpleHalter
                        (const lim)
                        (\_ _ _ -> lim)
                        (\l _ _ -> return $ if l <= 0 then Switch else Continue)
                        step
    where
        step l _ _ (State { curr_expr = CurrExpr Evaluate (Var _) }) = l - 1
        step l _ _ _ = l

{-# INLINE stdTimerHalter #-}
stdTimerHalter :: (MonadIO m, MonadIO m_run) => NominalDiffTime -> m (Halter m_run Int t)
stdTimerHalter ms = timerHalter ms Discard 10

{-# INLINE timerHalter #-}
timerHalter :: (MonadIO m, MonadIO m_run) => NominalDiffTime -> HaltC -> Int -> m (Halter m_run Int t)
timerHalter ms def ce = do
    curr <- liftIO $ getCurrentTime
    return $ mkSimpleHalter
                (const 0)
                (\_ _ _ -> 0)
                (stop curr)
                step
    where
        stop it v (Processed { accepted = acc }) _
            | v == 0
            , not (null acc) = do
                curr <- liftIO $ getCurrentTime
                let diff = diffUTCTime curr it

                if diff > ms
                    then return def
                    else return Continue
            | otherwise = return Continue

        step v _ _ _
            | v >= ce = 0
            | otherwise = v + 1

-- Orderer things
(<->) :: Orderer sov1 b1 t -> Orderer sov2 b2 t -> Orderer (C sov1 sov2) (b1, b2) t
or1 <-> or2 = Orderer {
      initPerStateOrder = \s ->
          let
              sov1 = initPerStateOrder or1 s
              sov2 = initPerStateOrder or2 s
          in
          C sov1 sov2

    , orderStates = \(C sov1 sov2) pr s ->
          let
              sov1' = orderStates or1 sov1 pr s
              sov2' = orderStates or2 sov2 pr s
          in
          (sov1', sov2')

    , updateSelected = \(C sov1 sov2) proc s ->
          let
              sov1' = updateSelected or1 sov1 proc s
              sov2' = updateSelected or2 sov2 proc s
          in
          C sov1' sov2'

    , stepOrderer = \(C sov1 sov2) proc xs s ->
            let
                sov1' = stepOrderer or1 sov1 proc xs s
                sov2' = stepOrderer or2 sov2 proc xs s
            in
            C sov1' sov2'
    }

ordComb :: (v1 -> v2 -> v3) -> Orderer sov1 v1 t  -> Orderer sov2 v2 t -> Orderer(C sov1 sov2) v3 t
ordComb f or1 or2 = Orderer {
      initPerStateOrder = \s ->
          let
              sov1 = initPerStateOrder or1 s
              sov2 = initPerStateOrder or2 s
          in
          C sov1 sov2

    , orderStates = \(C sov1 sov2) pr s ->
          let
              sov1' = orderStates or1 sov1 pr s
              sov2' = orderStates or2 sov2 pr s
          in
          f sov1' sov2'

    , updateSelected = \(C sov1 sov2) proc s ->
          let
              sov1' = updateSelected or1 sov1 proc s
              sov2' = updateSelected or2 sov2 proc s
          in
          C sov1' sov2'

    , stepOrderer = \(C sov1 sov2) proc xs s ->
          let
              sov1' = stepOrderer or1 sov1 proc xs s
              sov2' = stepOrderer or2 sov2 proc xs s
          in
          C sov1' sov2'
    }

nextOrderer :: Orderer () Int t
nextOrderer = mkSimpleOrderer (const ()) (\_ _ _ -> 0) (\v _ _ -> v)

-- | Continue execution on the state that has been picked the least in the past. 
pickLeastUsedOrderer :: Orderer Int Int t
pickLeastUsedOrderer = mkSimpleOrderer (const 0) (\v _ _ -> v) (\v _ _ -> v + 1)

-- | Floors and does bucket size
bucketSizeOrderer :: Int -> Orderer Int Int t
bucketSizeOrderer b =
    mkSimpleOrderer (const 0)
                    (\v _ _ -> floor (fromIntegral v / fromIntegral b :: Float))
                    (\v _ _ -> v + 1)

-- | Orders by the size (in terms of height) of (previously) symbolic ADT.
-- In particular, aims to first execute those states with a height closest to
-- the specified height.
adtHeightOrderer :: Int -> Maybe Name -> Orderer (HS.HashSet Name, Bool) Int t
adtHeightOrderer pref_height mn =
    (mkSimpleOrderer initial
                    order
                    (\v _ _ -> v))
                    { stepOrderer = step }
    where
        -- Normally, each state tracks the names of currently symbolic variables,
        -- but here we want all variables that were ever symbolic.
        -- To track this, we use a HashSet.
        -- The tracked bool is to speed up adjusting this hashset- if it is set to false,
        -- we do not update the hashset.  If it is set to true,
        -- after the next step the hashset will be updated, and the bool will be set
        -- back to false.
        -- This avoids repeated operations on the hashset after rules that we know
        -- will not add symbolic variables.
        initial s = (HS.fromList . map idName . E.symbolicIds . expr_env $ s, False)
        order (v, _) _ s =
            let
                m = maximum $ (-1):(HS.toList $ HS.map (flip adtHeight s) v)
                h = abs (pref_height - m)
            in
            h

        step (v, _) _ _
                      (State { curr_expr = CurrExpr _ (SymGen _ _) }) = (v, True)
        step(v, True) _ _ s =
            (v `HS.union` (HS.fromList . map idName . E.symbolicIds . expr_env $ s), False)
        step (v, _) _ _
                       (State { curr_expr = CurrExpr _ (Tick (NamedLoc n') (Var (Id vn _))) })
                | Just n <- mn, n == n' =
                    (HS.insert vn v, False)
        step  v _ _ _ = v

adtHeight :: Name -> State t -> Int
adtHeight n s@(State { expr_env = eenv })
    | Just (E.Sym _) <- v = 0
    | Just (E.Conc e) <- v =
        1 + adtHeight' e s
    | otherwise = 0
    where
        v = E.lookupConcOrSym n eenv

adtHeight' :: Expr -> State t -> Int
adtHeight' e s =
    let
        _:es = unApp e
    in
    maximum $ 0:map (\e' -> case e' of
                        Var (Id n _) -> adtHeight n s
                        _ -> 0) es

-- | Orders by the combined size of (previously) symbolic ADT.
-- In particular, aims to first execute those states with a combined ADT size closest to
-- the specified zize.
adtSizeOrderer :: Int -> Maybe Name -> Orderer (HS.HashSet Name, Bool) Int t
adtSizeOrderer pref_height mn =
    (mkSimpleOrderer initial
                    order
                    (\v _ _ -> v))
                    { stepOrderer = step }
    where
        -- Normally, each state tracks the names of currently symbolic variables,
        -- but here we want all variables that were ever symbolic.
        -- To track this, we use a HashSet.
        -- The tracked bool is to speed up adjusting this hashset- if it is set to false,
        -- we do not update the hashset.  If it is set to true,
        -- after the next step the hashset will be updated, and the bool will be set
        -- back to false.
        -- This avoids repeated operations on the hashset after rules that we know
        -- will not add symbolic variables.
        initial s = (HS.fromList . map idName . E.symbolicIds . expr_env $ s, False)
        order (v, _) _ s =
            let
                m = sum (HS.toList $ HS.map (flip adtSize s) v)
                h = abs (pref_height - m)
            in
            h

        step (v, _) _ _
                      (State { curr_expr = CurrExpr _ (SymGen _ _) }) = (v, True)
        step (v, True) _ _ s =
            (v `HS.union` (HS.fromList . map idName . E.symbolicIds . expr_env $ s), False)
        step (v, _) _ _
                       (State { curr_expr = CurrExpr _ (Tick (NamedLoc n') (Var (Id vn _))) })
                | Just n <- mn, n == n' = (HS.insert vn v, False)
        step v _ _ _ = v

adtSize :: Name -> State t -> Int
adtSize n s@(State { expr_env = eenv })
    | Just (E.Sym _) <- v = 0
    | Just (E.Conc e) <- v =
        1 + adtSize' e s
    | otherwise = 0
    where
        v = E.lookupConcOrSym n eenv

adtSize' :: Expr -> State t -> Int
adtSize' e s =
    let
        _:es = unApp e
    in
    sum $ 0:map (\e' -> case e' of
                        Var (Id n _) -> adtSize n s
                        _ -> 0) es

-- | Orders by the number of Path Constraints
pcSizeOrderer :: Int  -- ^ What size should we prioritize?
              -> Orderer () Int t
pcSizeOrderer pref_height = mkSimpleOrderer (const ())
                                            order
                                            (\v _ _ -> v)
    where
        order _ _ s =
            let
                m = PC.number (path_conds s)
                h = abs (pref_height - m)
            in
            h

data IncrAfterNTr sov = IncrAfterNTr { steps_since_change :: Int
                                     , incr_by :: Int
                                     , underlying :: sov }

-- | Wraps an existing Orderer, and increases it's value by 1, every time
-- it doesn't change after N steps 
incrAfterN :: (Eq sov, Enum b) => Int -> Orderer sov b t -> Orderer (IncrAfterNTr sov) b t
incrAfterN n ord = (mkSimpleOrderer initial order update) { stepOrderer = step }
    where
        initial s =
            IncrAfterNTr { steps_since_change = 0
                         , incr_by = 0
                         , underlying = initPerStateOrder ord s }

        order sov pr s =
            let
                b = orderStates ord (underlying sov) pr s
            in
            succNTimes (incr_by sov) b

        update sov pr s =
            sov { underlying = updateSelected ord (underlying sov) pr s }

        step sov pr xs s
            | steps_since_change sov >= n =
                sov' { incr_by = incr_by sov' + 1
                     , steps_since_change = 0 }
            | under /= under' =
                sov' { steps_since_change = 0 }
            | otherwise =
                sov' { steps_since_change = steps_since_change sov' + 1}
            where
                under = underlying sov
                under' = stepOrderer ord under pr xs s
                sov' = sov { underlying = under' }

succNTimes :: Enum b => Int -> b -> b
succNTimes x b
    | x <= 0 = b
    | otherwise = succNTimes (x - 1) (succ b)

-- | Wraps an existing orderer, and divides its value by 2 if true_assert is true
quotTrueAssert :: Integral b => Orderer sov b t -> Orderer sov b t
quotTrueAssert ord = (mkSimpleOrderer (initPerStateOrder ord)
                                      order
                                      (updateSelected ord))
                                      { stepOrderer = stepOrderer ord}
    where
        order sov pr s =
            let
                b = orderStates ord sov pr s
            in
            if true_assert s then b `quot` 2 else b

--------
--------

{-# SPECIALIZE runReducer :: Ord b =>
                             Reducer IO rv t
                          -> Halter IO hv t
                          -> Orderer sov b t
                          -> State t
                          -> Bindings
                          -> IO (Processed (State t), Bindings)
    #-}
{-# SPECIALIZE runReducer :: Ord b =>
                             Reducer (SM.StateT PrettyGuide IO) rv t
                          -> Halter (SM.StateT PrettyGuide IO) hv t
                          -> Orderer sov b t
                          -> State t
                          -> Bindings
                          -> SM.StateT PrettyGuide IO (Processed (State t), Bindings)
    #-}
-- | Uses a passed Reducer, Halter and Orderer to execute the reduce on the State, and generated States
runReducer :: (Monad m, Ord b) =>
              Reducer m rv t
           -> Halter m hv t
           -> Orderer sov b t
           -> State t
           -> Bindings
           -> m (Processed (State t), Bindings)
runReducer red hal ord s b = do
    let pr = Processed {accepted = [], discarded = []}
    let s' = ExState { state = s
                     , reducer_val = initReducer red s
                     , halter_val = initHalt hal s
                     , order_val = initPerStateOrder ord s }

    (states, b') <- runReducer' red hal ord pr s' b M.empty
    return (states, b')

runReducer' :: (Monad m, Ord b)
            => Reducer m rv t
            -> Halter m hv t
            -> Orderer sov b t
            -> Processed (State t)
            -> ExState rv hv sov t
            -> Bindings
            -> M.Map b [ExState rv hv sov t]
            -> m (Processed (State t), Bindings)
runReducer' red hal ord pr rs@(ExState { state = s, reducer_val = r_val, halter_val = h_val, order_val = o_val }) b xs = do
    hc <- stopRed hal h_val pr s
    case () of
        ()
            | hc == Accept ->
                let
                    pr' = pr {accepted = state rs:accepted pr}
                    jrs = minState ord pr' xs
                in
                case jrs of
                    Just (rs', xs') -> do
                        onAccept red s r_val
                        switchState red hal ord pr' rs' b xs'
                    Nothing -> return (pr', b)
            | hc == Discard ->
                let
                    pr' = pr {discarded = state rs:discarded pr}
                    jrs = minState ord pr' xs
                in
                case jrs of
                    Just (rs', xs') ->
                        switchState red hal ord pr' rs' b xs'
                    Nothing -> return (pr', b)
            | hc == Switch ->
                let
                    k = orderStates ord (order_val rs') pr (state rs)
                    rs' = rs { order_val = updateSelected ord (order_val rs) pr (state rs) }

                    Just (rs'', xs') = minState ord pr (M.insertWith (++) k [rs'] xs)
                in
                switchState red hal ord pr rs'' b xs'
            | otherwise -> do
                (_, reduceds, b') <- redRules red r_val s b
                let reduceds' = map (\(r, rv) -> (r {num_steps = num_steps r + 1}, rv)) reduceds

                    r_vals = if length reduceds' > 1
                                then updateWithAll red reduceds' ++ error "List returned by updateWithAll is too short."
                                else map snd reduceds

                    reduceds_h_vals = map (\(r, _) -> (r, h_val)) reduceds'
                    h_vals = if length reduceds' > 1
                                then updateHalterWithAll hal reduceds_h_vals ++ error "List returned by updateWithAll is too short."
                                else repeat h_val

                    new_states = map fst reduceds'

                    mod_info = map (\(s', r_val', h_val') ->
                                        rs { state = s'
                                           , reducer_val = r_val'
                                           , halter_val = stepHalter hal h_val' pr new_states s'
                                           , order_val = stepOrderer ord o_val pr new_states s'}) $ zip3 new_states r_vals h_vals




                case mod_info of
                    (s_h:ss_tail) -> do
                        let
                            b_ss_tail =
                                L.map (\s' ->
                                    let
                                        n_b = orderStates ord (order_val s') pr (state s')
                                    in
                                    (n_b, s')) ss_tail

                            xs' = foldr (\(or_b, s') -> M.insertWith (++) or_b [s']) xs b_ss_tail

                        runReducer' red hal ord pr s_h b' xs'
                    [] -> runReducerList red hal ord pr xs b'

switchState :: (Monad m, Ord b)
            => Reducer m rv t
            -> Halter m hv t
            -> Orderer sov b t
            -> Processed (State t)
            -> ExState rv hv sov t
            -> Bindings
            -> M.Map b [ExState rv hv sov t]
            -> m (Processed (State t), Bindings)
switchState red hal ord pr rs b xs
    | not $ discardOnStart hal (halter_val rs') pr (state rs') =
        runReducer' red hal ord pr rs' b xs
    | otherwise =
        runReducerListSwitching red hal ord (pr {discarded = state rs':discarded pr}) xs b
    where
        rs' = rs { halter_val = updatePerStateHalt hal (halter_val rs) pr (state rs) }

-- To be used when we we need to select a state without switching 
runReducerList :: (Monad m, Ord b)
               => Reducer m rv t
               -> Halter m hv t
               -> Orderer sov b t
               -> Processed (State t)
               -> M.Map b [ExState rv hv sov t]
               -> Bindings
               -> m (Processed (State t), Bindings)
runReducerList red hal ord pr m binds =
    case minState ord pr m of
        Just (rs, m') ->
            let
                rs' = rs { halter_val = updatePerStateHalt hal (halter_val rs) pr (state rs) }
            in
            runReducer' red hal ord pr rs' binds m'
        Nothing -> return (pr, binds)

-- To be used when we are possibly switching states 
runReducerListSwitching :: (Monad m, Ord b)
                        => Reducer m rv t
                        -> Halter m hv t
                        -> Orderer sov b t
                        -> Processed (State t)
                        -> M.Map b [ExState rv hv sov t]
                        -> Bindings
                        -> m (Processed (State t), Bindings)
runReducerListSwitching red hal ord pr m binds =
    case minState ord pr m of
        Just (x, m') -> switchState red hal ord pr x binds m'
        Nothing -> return (pr, binds)

-- Uses the Orderer to determine which state to continue execution on.
-- Returns that State, and a list of the rest of the states 
minState :: Ord b
         => Orderer sov b t
         -> Processed (State t)
         -> M.Map b [ExState rv hv sov t]
         -> Maybe ((ExState rv hv sov t), M.Map b [ExState rv hv sov t])
minState ord pr m =
    case getState m of
      Just (k, x:[]) -> Just (x, M.delete k m)
      Just (k, x:xs) -> Just (x, M.insert k xs m)
      Just (k, []) -> minState ord pr $ M.delete k m
      Nothing -> Nothing

