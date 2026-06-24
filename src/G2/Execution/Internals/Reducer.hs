{-# LANGUAGE CPP, GADTs, RankNTypes #-}

module G2.Execution.Internals.Reducer where

import G2.Language
import qualified Control.Monad.State as SM
import qualified Data.Map as M

#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
import GHC.Driver.Monad
#else
import GhcMonad (GhcT, liftGhcT)
#endif

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

exStateToState :: ExState rv hv sov t -> State t
exStateToState = state

data GotUnknown = GotUnknown | NoUnknowns deriving (Eq, Show)

-- | Keeps track of type a's that have either been accepted or dropped
data Processed acc dis = Processed { accepted :: [acc]
                                   , discarded :: [dis]
                                   , unknown_state :: GotUnknown -- ^ Set to true if solving a State returns unknown
                                   }

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
data HaltC = Discard String -- ^ Switch to evaluating a new state, and reject the current state
           | Accept -- ^ Switch to evaluating a new state, and accept the current state
           | Switch -- ^ Switch to evaluating a new state, but continue evaluating the current state later
           | Continue -- ^ Continue evaluating the current State
           deriving (Ord, Show, Read)

instance Eq HaltC where
    Discard _ == Discard _ = True
    Accept == Accept = True
    Switch == Switch = True
    Continue == Continue = True
    _ == _ = False

type InitReducer rv t = State t -> rv
type RedRules m rv t = rv -> State t -> Bindings -> m (ReducerRes, [(State t, rv)], Bindings)


-- | A Reducer is used to define a set of Reduction Rules.
-- Reduction Rules take a `State`, and output new `State`s.
-- The reducer value, rv, can be used to track extra information, on a per `State` basis.
data Reducer m rv t = Reducer {
        -- | Initializes the reducer value.
          initReducer :: InitReducer rv t

        -- | Takes a State, and performs the appropriate Reduction Rule.
        , redRules :: RedRules m rv t

        -- | After a reducer returns multiple states,
        -- gives an opportunity to update with all States and Reducer values's,
        -- visible.
        -- Errors if the returned list is too short.
        -- If only one state is returned by all reducers, updateWithAll does not run.
        , updateWithAll :: [State t] -> [State t]

        -- Action to run after a State is accepted.
        , onAccept :: State t -> Bindings -> rv -> m (State t, Bindings)

        -- Action to run after a State is solved.
        , onSolved :: m ()

        -- Action to run after a State is discared.
        , onDiscard :: forall b rv1 hv sov . String -> M.Map b [ExState rv1 hv sov t] -> State t -> rv -> m ()

        -- | Action to run after execution of all states has terminated.
        , afterRed :: m ()

    }

-- | A simple, default reducer.
-- `updateWithAll` does not change or adjust the reducer values.
-- `onAccept` and `afterRed` immediately returns the empty tuple.
mkSimpleReducer :: Monad m => InitReducer rv t -> RedRules m rv t -> Reducer m rv t
mkSimpleReducer init_red red_rules =
    Reducer {
      initReducer = init_red
    , redRules = red_rules
    , updateWithAll = id
    , onAccept = \s b _ -> return (s, b)
    , onSolved = return ()
    , onDiscard = \_ _ _ _ -> return ()
    , afterRed = return ()
    }
{-# INLINE mkSimpleReducer #-}

-- | Lift a reducer from a component monad to a constructed monad. 
liftReducer :: (Monad m1, SM.MonadTrans m2) => Reducer m1 rv t -> Reducer (m2 m1) rv t
liftReducer r = Reducer { initReducer = initReducer r
                        , redRules = \rv s b -> SM.lift ((redRules r) rv s b)
                        , updateWithAll = updateWithAll r
                        , onAccept = \s b rv -> SM.lift ((onAccept r) s b rv)
                        , onSolved = SM.lift (onSolved r)
                        , onDiscard = \dis_nme s xs rv -> SM.lift ((onDiscard r) dis_nme s xs rv)
                        , afterRed = SM.lift (afterRed r)}

-- | Lift a reducer from a component monad to a constructed monad. 
liftReducerGhcT :: Monad m => Reducer m rv t -> Reducer (GhcT m) rv t
liftReducerGhcT r = Reducer { initReducer = initReducer r
                        , redRules = \rv s b -> liftGhcT ((redRules r) rv s b)
                        , updateWithAll = updateWithAll r
                        , onAccept = \s b rv -> liftGhcT ((onAccept r) s b rv)
                        , onSolved = liftGhcT (onSolved r)
                        , onDiscard = \dis_nme s xs rv -> liftGhcT ((onDiscard r) dis_nme s xs rv)
                        , afterRed = liftGhcT (afterRed r)}

-- | Lift a SomeReducer from a component monad to a constructed monad. 
liftSomeReducer :: (Monad m1, SM.MonadTrans m2) => SomeReducer m1 t -> SomeReducer (m2 m1) t
liftSomeReducer (SomeReducer r) = SomeReducer (liftReducer r )

type InitHalter hv t = State t -> hv
type UpdatePerStateHalt hv r t = hv -> Processed r (State t) -> State t -> hv
type StopRed m hv r t = hv -> Processed r (State t)  -> State t -> m HaltC
type StepHalter hv r t = hv -> Processed r (State t) -> [State t] -> State t -> hv

-- | Determines when to stop evaluating a state
-- The halter value, hv, can be used to track extra information, on a per `State` basis.
data Halter m hv r t = Halter {
    -- | Initializes each state halter value
      initHalt :: InitHalter hv t

    -- | Runs whenever we switch to evaluating a different state,
    -- to update the halter value of that new state
    , updatePerStateHalt :: UpdatePerStateHalt hv r t

    -- | Runs when we start execution on a state, immediately after
    -- `updatePerStateHalt`.  Allows a State to be discarded right
    -- before execution is about to (re-)begin.
    -- Return True if execution should proceed, False to discard
    , discardOnStart :: hv -> Processed r (State t) -> State t -> Bool

    -- | Determines whether to continue reduction on the current state
    , stopRed :: StopRed m hv r t

    -- | Takes a state, and updates its halter record field
    , stepHalter :: StepHalter hv r t

    -- | After multiple states, are returned
    -- gives an opportunity to update halters with all States and halter values visible.
    -- Errors if the returned list is too short.
    -- If only one state is returned, updateHalterWithAll does not run.
    , updateHalterWithAll :: [(State t, hv)] -> [hv]

    -- Runs before selecting a new state to filter down possiblities
    , filterAllStates :: forall b rv hv1 sov . M.Map b [ExState rv hv1 sov t] -> M.Map b [ExState rv hv1 sov t]

    }

-- | A simple, default halter.
mkSimpleHalter :: Monad m => InitHalter hv t -> UpdatePerStateHalt hv r t -> StopRed m hv r t -> StepHalter hv r t -> Halter m hv r t
mkSimpleHalter initial update stop step = Halter { initHalt = initial
                                                 , updatePerStateHalt = update
                                                 , discardOnStart = \_ _ _ -> False
                                                 , stopRed = stop
                                                 , stepHalter = step
                                                 , updateHalterWithAll = map snd
                                                 , filterAllStates = id }
{-# INLINE mkSimpleHalter #-}

-- | Lift a halter from a component monad to a constructed monad. 
liftHalter :: (Monad m1, SM.MonadTrans m2) => Halter m1 rv r t -> Halter (m2 m1) rv r t
liftHalter h = Halter { initHalt = initHalt h
                      , updatePerStateHalt = updatePerStateHalt h
                      , discardOnStart = discardOnStart h
                      , stopRed = \hv pr s -> SM.lift ((stopRed h) hv pr s)
                      , stepHalter = stepHalter h
                      , updateHalterWithAll = updateHalterWithAll h
                      , filterAllStates = id }

liftHalterGhcT :: Monad m => Halter m rv r t -> Halter (GhcT m) rv r t
liftHalterGhcT h = Halter { initHalt = initHalt h
                      , updatePerStateHalt = updatePerStateHalt h
                      , discardOnStart = discardOnStart h
                      , stopRed = \hv pr s -> liftGhcT ((stopRed h) hv pr s)
                      , stepHalter = stepHalter h
                      , updateHalterWithAll = updateHalterWithAll h
                      , filterAllStates = id }

-- | Lift a SomeHalter from a component monad to a constructed monad. 
liftSomeHalter :: (Monad m1, SM.MonadTrans m2) => SomeHalter m1 r t -> SomeHalter (m2 m1) r t
liftSomeHalter (SomeHalter r) = SomeHalter (liftHalter r)

{-# INLINE mkStoppingHalter #-}
mkStoppingHalter :: Monad m => StopRed m () r t -> Halter m () r t
mkStoppingHalter stop =
            mkSimpleHalter
                (const ())
                (\_ _ _ -> ())
                stop
                (\_ _ _ _ -> ())

type InitOrderer sov t = State t -> sov
type OrderStates m sov b r t = sov -> Processed r (State t) -> State t -> m b
type UpdateSelected sov r t = sov -> Processed r (State t) -> State t -> sov

-- | Picks an order to evaluate the states, to allow prioritizing some over others.
-- The orderer value, sov, can be used to track extra information, on a per `State` basis.
-- The ordering type b, is used to determine what order to execute the states in.
-- In practice, `b` must be an instance of `Ord`.  When the orderer is called, the `State` corresponding
-- to the minimal `b` is executed.
data Orderer m sov b r t = Orderer {
    -- | Initializing the per state ordering value 
      initPerStateOrder :: InitOrderer sov t

    -- | Assigns each state some value of an ordered type, and then proceeds with execution on the
    -- state assigned the minimal value
    , orderStates :: OrderStates m sov b r t

    -- | Run on the selected state, to update it's sov field
    , updateSelected :: UpdateSelected sov r t

    -- | Run on the state at each step, to update it's sov field
    , stepOrderer :: sov -> Processed r (State t) -> [State t] -> State t -> m sov
    }

-- | A simple, default orderer.
mkSimpleOrderer :: Monad m => InitOrderer sov t -> OrderStates m sov b r t -> UpdateSelected sov r t -> Orderer m sov b r t
mkSimpleOrderer initial order update = Orderer { initPerStateOrder = initial
                                               , orderStates = order
                                               , updateSelected = update
                                               , stepOrderer = \sov _ _ _ -> return sov}

-- | Lift a Orderer from a component monad to a constructed monad. 
liftOrderer :: (Monad m1, SM.MonadTrans m2) => Orderer m1 sov b r t -> Orderer (m2 m1) sov b r t
liftOrderer r = Orderer { initPerStateOrder = initPerStateOrder r
                        , orderStates = \sov pr s -> SM.lift ((orderStates r) sov pr s)
                        , updateSelected = updateSelected r
                        , stepOrderer = \sov pr xs s -> SM.lift ((stepOrderer r) sov pr xs s) }

-- | Lift a Orderer from a component monad to a constructed monad. 
liftOrdererGhcT :: Monad m => Orderer m sov b r t -> Orderer (GhcT m) sov b r t
liftOrdererGhcT r = Orderer { initPerStateOrder = initPerStateOrder r
                        , orderStates = \sov pr s -> liftGhcT ((orderStates r) sov pr s)
                        , updateSelected = updateSelected r
                        , stepOrderer = \sov pr xs s -> liftGhcT ((stepOrderer r) sov pr xs s) }

-- | Lift a liftSomeOrderer from a component monad to a constructed monad. 
liftSomeOrderer :: (Monad m1, SM.MonadTrans m2) => SomeOrderer m1 r t -> SomeOrderer (m2 m1) r t
liftSomeOrderer (SomeOrderer r) = SomeOrderer (liftOrderer r)

getState :: M.Map b [s] -> Maybe (b, [s])
getState = M.lookupMin

-- | Hide the details of a Reducer's reducer value.
data SomeReducer m t where
    SomeReducer :: forall m rv t . Reducer m rv t -> SomeReducer m t

-- | Hide the details of a Halter's halter value.
data SomeHalter m r t where
    SomeHalter :: forall m hv r t . Halter m hv r t -> SomeHalter m r t

-- | Hide the details of an Orderer's orderer value and ordering type.
data SomeOrderer m r t where
    SomeOrderer :: forall m sov b r t . Ord b => Orderer m sov b r t -> SomeOrderer m r t

