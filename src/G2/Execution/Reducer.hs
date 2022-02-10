{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module G2.Execution.Reducer ( Reducer (..)
                            , Halter (..)
                            , Orderer (..)
                            , MinOrderer (..)
                            , ToOrderer (..)

                            , Processed (..)
                            , mapProcessed

                            , ReducerRes (..)
                            , HaltC (..)

                            , SomeReducer (..)
                            , SomeHalter (..)
                            , SomeOrderer (..)

                            , EquivTracker (..)

                            -- Reducers
                            , RCombiner (..)
                            , StdRed (..)
                            , ConcSymReducer (..)
                            , NonRedPCRed (..)
                            , NonRedPCRedConst (..)
                            , TaggerRed (..)
                            , Logger (..)
                            , prettyLogger
                            , getLogger
                            , PrettyLogger (..)
                            , LimLogger (..)
                            , PredicateLogger (..)
                            , OnlyPath (..)

                            , (<~)
                            , (<~?)
                            , (<~|)

                            -- Halters
                            , SWHNFHalter (..)
                            , AcceptIfViolatedHalter (..)
                            , HCombiner (..)
                            , ZeroHalter (..)
                            , DiscardIfAcceptedTag (..)
                            , MaxOutputsHalter (..)
                            , SwitchEveryNHalter (..)
                            , BranchAdjSwitchEveryNHalter (..)
                            , RecursiveCutOff (..)
                            , VarLookupLimit (..)
                            , BranchAdjVarLookupLimit (..)
                            , TimerHalter (if_time_out)
                            , timerHalter
                            , OnlyIf (..)

                            -- Orderers
                            , OCombiner (..)
                            , FlexOrdCombiner (..)
                            , NextOrderer (..)
                            , PickLeastUsedOrderer (..)
                            , BucketSizeOrderer (..)
                            , CaseCountOrderer (..)
                            , SymbolicADTOrderer (..)
                            , ADTHeightOrderer (..)
                            , ADTSizeOrderer (..)
                            , PCSizeOrderer (..)
                            , IncrAfterN (..)
                            , QuotTrueAssert (..)
                            , RandomOrderer (..)
                            , mkRandomOrderer
                            , getRandomOrderer
                            , WeightedRandomOrderer
                            , mkWeightedRandomOrderer
                            , getWeightedRandomOrderer

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

import Data.Foldable
import Data.Hashable
import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid ((<>))
import qualified Data.List as L
import Data.Tuple
import Data.Time.Clock
import System.Directory
import System.Random

import GHC.Generics (Generic)

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

-- | A Reducer is used to describe a set of Reduction Rules.
-- Reduction Rules take a State, and output new states.
-- The type parameter r is used to disambiguate between different producers.
-- To create a new reducer, define some new type, and use it as r. 
-- The reducer value, rv, can be used to track special, per Reducer, information.
class Reducer r rv t | r -> rv where
    -- | Initialized the reducer value
    initReducer :: r -> State t -> rv

    -- | Takes a State, and performs the appropriate Reduction Rule
    redRules :: r -> rv -> State t -> Bindings -> IO (ReducerRes, [(State t, rv)], Bindings, r) 
    
    -- | After a reducer returns multiple states,
    -- gives an opportunity to update with all States and Reducer Val's,
    -- output by all Reducer's, visible
    -- Errors if the returned list is too short.
    -- If only one state is returned by all reducers, updateWithAll does not run.
    {-# INLINE updateWithAll #-}
    updateWithAll :: r -> [(State t, rv)] -> [rv]
    updateWithAll _ = map snd 

    onAccept :: r -> State t -> rv -> IO ()
    onAccept _ _ _ = return ()

-- | Determines when to stop evaluating a state
-- The type parameter h is used to disambiguate between different producers.
-- To create a new Halter, define some new type, and use it as h.
class Halter h hv t | h -> hv where
    -- | Initializes each state halter value
    initHalt :: h -> State t -> hv

    -- | Runs whenever we switch to evaluating a different state,
    -- to update the halter value of that new state
    updatePerStateHalt :: h -> hv -> Processed (State t) -> State t -> hv

    -- | Runs when we start execution on a state, immediately after
    -- `updatePerStateHalt`.  Allows a State to be discarded right
    -- before execution is about to (re-)begin.
    -- Return True if execution should proceed, False to discard
    discardOnStart :: h -> hv -> Processed (State t) -> State t -> Bool
    discardOnStart _ _ _ _ = False

    -- | Determines whether to continue reduction on the current state
    stopRed :: h -> hv -> Processed (State t) -> State t -> IO HaltC

    -- | Takes a state, and updates its halter record field
    stepHalter :: h -> hv -> Processed (State t) -> [State t] -> State t -> hv


    -- | After multiple states, are returned
    -- gives an opportunity to update halters with all States and halter values visible.
    -- Errors if the returned list is too short.
    -- If only one state is returned, updateHalterWithAll does not run.
    {-# INLINE updateHalterWithAll #-}
    updateHalterWithAll :: h -> [(State t, hv)] -> [hv]
    updateHalterWithAll _ = map snd 

-- | Picks an order to evaluate the states, to allow prioritizing some over others 
-- The type parameter or is used to disambiguate between different producers.
-- To create a new reducer, define some new type, and use it as or.
class Ord b => Orderer or sov b t | or -> sov, or -> b where
    -- | Initializing the per state ordering value 
    initPerStateOrder :: or -> State t -> sov

    -- | Assigns each state some value of an ordered type, and then proceeds with execution on the
    -- state assigned the minimal value
    orderStates :: or -> sov -> Processed (State t) -> State t -> (b, or)

    -- | Run on the selected state, to update it's sov field
    updateSelected :: or -> sov -> Processed (State t) -> State t -> sov

    -- | Run on the state at each step, to update it's sov field
    stepOrderer :: or -> sov -> Processed (State t) -> [State t] -> State t -> sov 
    stepOrderer _ sov _ _ _ = sov

    getState :: forall s . or -> Processed (State t) -> M.Map b [s] -> Maybe (b, [s])
    getState _ _ = M.lookupMin

class Ord b => MinOrderer or sov b t | or -> sov, or -> b where
    -- | Initializing the per state ordering value 
    minInitPerStateOrder :: or -> State t -> sov

    -- | Assigns each state some value of an ordered type, and then proceeds with execution on the
    -- state assigned the minimal value
    minOrderStates :: or -> sov -> Processed (State t) -> State t -> (b, or)

    -- | Run on the selected state, to update it's sov field
    minUpdateSelected :: or -> sov -> Processed (State t) -> State t -> sov

    -- | Run on the state at each step, to update it's sov field
    minStepOrderer :: or -> sov -> Processed (State t) -> [State t] -> State t -> sov 
    minStepOrderer _ sov _ _ _ = sov

newtype ToOrderer min_ord = ToOrderer min_ord

instance (MinOrderer min_ord sov b t, Ord b) => Orderer (ToOrderer min_ord) sov b t where
    initPerStateOrder (ToOrderer min_ord) = minInitPerStateOrder min_ord
    orderStates (ToOrderer min_ord) sov pr = fmap ToOrderer . minOrderStates min_ord sov pr
    updateSelected (ToOrderer min_ord) = minUpdateSelected min_ord
    stepOrderer (ToOrderer min_ord) = minStepOrderer min_ord
    getState _ _ = M.lookupMin

data SomeReducer t where
    SomeReducer :: forall r rv t . Reducer r rv t => r -> SomeReducer t

data SomeHalter t where
    SomeHalter :: forall h hv t . Halter h hv t => h -> SomeHalter t

data SomeOrderer t where
    SomeOrderer :: forall or sov b t . Orderer or sov b t => or -> SomeOrderer t

-- | Combines reducers in various ways
-- updateWithAll is called by all Reducers, regardless of which combinator is used
data RCombiner r1 r2 = r1 :<~ r2 -- ^ Apply r2, followed by r1.  Takes the leftmost update to r1
                     | r1 :<~? r2 -- ^ Apply r2, apply r1 only if r2 returns NoProgress
                     | r1 :<~| r2 -- ^ Apply r2, apply r1 only if r2 returns Finished
                     | r1 :|: r2 -- ^ Apply both r1 and r2 to the initial states
                     deriving (Eq, Show, Read)

-- We use RC to combine the reducer values for RCombiner
-- We should never define any other instance of Reducer with RC, or export it
-- because this could lead to undecidable instances
data RC a b = RC a b

instance (Reducer r1 rv1 t, Reducer r2 rv2 t) => Reducer (RCombiner r1 r2) (RC rv1 rv2) t where
    initReducer (r1 :<~ r2) = initReducerGen r1 r2
    initReducer (r1 :<~? r2) = initReducerGen r1 r2
    initReducer (r1 :<~| r2) = initReducerGen r1 r2
    initReducer (r1 :|: r2) = initReducerGen r1 r2


    redRules (r1 :<~ r2) (RC rv1 rv2) s b = do
        (rr2, srv2, b', r2') <- redRules r2 rv2 s b
        (rr1, srv1, b'', r1') <- redRulesToStates r1 rv1 srv2 b'

        return (progPrioritizer rr1 rr2, srv1, b'', r1' :<~ r2')

    redRules (r1 :<~? r2) (RC rv1 rv2) s b = do
        (rr2, srv2, b', r2') <- redRules r2 rv2 s b
        let (s', rv2') = unzip srv2

        case rr2 of
            NoProgress -> do
                (rr1, ss, b'', r1') <- redRulesToStates r1 rv1 srv2 b'
                return (rr1, ss, b'', r1' :<~? r2')
            _ -> return (rr2, zip s' (map (uncurry RC) (zip (repeat rv1) rv2')), b', r1 :<~? r2')

    redRules (r1 :<~| r2) (RC rv1 rv2) s b = do
        (rr2, srv2, b', r2') <- redRules r2 rv2 s b
        let (s', rv2') = unzip srv2

        case rr2 of
            Finished -> do
                (rr1, ss, b'', r1') <- redRulesToStates r1 rv1 srv2 b'
                return (rr1, ss, b'', r1' :<~| r2')
            _ -> return (rr2, zip s' (map (uncurry RC) (zip (repeat rv1) rv2')), b', r1 :<~| r2')

    redRules (r1 :|: r2) (RC rv1 rv2) s b = do
        (rr2, srv2, b', r2') <- redRules r2 rv2 s b
        (rr1, srv1, b'', r1') <- redRules r1 rv1 s b'

        let srv2' = map (\(s, rv2_) -> (s, RC rv1 rv2_) ) srv2
            srv1' = map (\(s, rv1_) -> (s, RC rv1_ rv2) ) srv1

        return (progPrioritizer rr1 rr2, srv2' ++ srv1', b'', r1' :|: r2')

    {-# INLINE updateWithAll #-}
    updateWithAll (r1 :<~ r2) = updateWithAllRC r1 r2
    updateWithAll (r1 :<~? r2) = updateWithAllRC r1 r2
    updateWithAll (r1 :<~| r2) = updateWithAllRC r1 r2
    updateWithAll (r1 :|: r2) = updateWithAllRC r1 r2

    onAccept (r1 :<~ r2) s (RC rv1 rv2) = do
        onAccept r1 s rv1
        onAccept r2 s rv2
    onAccept (r1 :<~? r2) s (RC rv1 rv2) = do
        onAccept r1 s rv1
        onAccept r2 s rv2
    onAccept (r1 :<~| r2) s (RC rv1 rv2) = do
        onAccept r1 s rv1
        onAccept r2 s rv2
    onAccept (r1 :|: r2) s (RC rv1 rv2) = do
        onAccept r1 s rv1
        onAccept r2 s rv2


initReducerGen :: (Reducer r1 rv1 t, Reducer r2 rv2 t) => r1 -> r2 -> State t -> RC rv1 rv2
initReducerGen r1 r2 s =
    let
        rv1 = initReducer r1 s
        rv2 = initReducer r2 s
    in
    RC rv1 rv2

{-# INLINE updateWithAllRC #-}
updateWithAllRC :: (Reducer r1 rv1 t, Reducer r2 rv2 t) => r1 -> r2 -> [(State t, RC rv1 rv2)] -> [RC rv1 rv2]
updateWithAllRC r1 r2 srv =
    let
        srv1 = map (\(s, RC rv1 _) -> (s, rv1)) srv
        srv2 = map (\(s, RC _ rv2) -> (s, rv2)) srv

        rv1' = updateWithAll r1 srv1
        rv2' = updateWithAll r2 srv2
    in
    map (uncurry RC) $ zip rv1' rv2'

redRulesToStatesAux :: Reducer r rv t => r -> rv -> Bindings -> (State t, rv2) -> IO (Bindings, (ReducerRes, [(State t, RC rv rv2)], r))
redRulesToStatesAux r rv1 b (is, rv2) = do
        (rr_, is', b', r') <- redRules r rv1 is b
        return (b', (rr_, map (\(is'', rv1') -> (is'', RC rv1' rv2) ) is', r'))
    
redRulesToStates :: Reducer r rv t => r -> rv -> [(State t, rv2)] -> Bindings -> IO (ReducerRes, [(State t, RC rv rv2)], Bindings, r)
redRulesToStates r rv1 s b = do
    let redRulesToStatesAux' = redRulesToStatesAux r rv1
    (b', rs) <- MD.mapMAccumB redRulesToStatesAux' b s

    let (rr, s', r') = L.unzip3 rs

    let rf = foldr progPrioritizer NoProgress rr

    return $ (rf, concat s', b', head r')

{-# INLINE (<~) #-}
-- | Combines two @`SomeReducer`@s with a @`:<~`@
(<~) :: SomeReducer t -> SomeReducer t -> SomeReducer t
SomeReducer r1 <~ SomeReducer r2 = SomeReducer (r1 :<~ r2)

{-# INLINE (<~?) #-}
-- | Combines two @`SomeReducer`@s with a @`:<~?`@
(<~?) :: SomeReducer t -> SomeReducer t -> SomeReducer t
SomeReducer r1 <~? SomeReducer r2 = SomeReducer (r1 :<~? r2)

{-# INLINE (<~|) #-}
-- | Combines two @`SomeReducer`@s with a @`:<~|`@
(<~|) :: SomeReducer t -> SomeReducer t -> SomeReducer t
SomeReducer r1 <~| SomeReducer r2 = SomeReducer (r1 :<~| r2)

data StdRed solver simplifier = StdRed Sharing solver simplifier

instance (Solver solver, Simplifier simplifier) => Reducer (StdRed solver simplifier) () t where
    initReducer _ _ = ()

    redRules stdr@(StdRed share solver simplifier) _ s b = do
        (r, s', b') <- stdReduce share solver simplifier s b
        
        return (if r == RuleIdentity then Finished else InProgress, s', b', stdr)

data ConcSymReducer = ConcSymReducer

-- Maps higher order function calls to symbolic replacements.
-- This allows the same call to be replaced by the same Id consistently.
-- relocated from Equiv.G2Calls
-- TODO dormant is 0 if execution can happen now
-- at what point do dormant values get assigned?
-- EquivTracker probably the wrong level for handling this
data EquivTracker = EquivTracker { higher_order :: HM.HashMap Expr Id
                                 , saw_tick :: Maybe Int
                                 , total :: HS.HashSet Name
                                 , finite :: HS.HashSet Name
                                 , dc_path :: [(DataCon, Int, Int)]
                                 , folder_name :: String } deriving (Show, Eq, Generic)

instance Hashable EquivTracker

-- Forces a lone symbolic variable with a type corresponding to an ADT
-- to evaluate to some value of that ADT
instance Reducer ConcSymReducer () EquivTracker where
    initReducer _ _ = ()

    redRules red _
                   s@(State { curr_expr = CurrExpr _ (Var i@(Id n t))
                            , expr_env = eenv
                            , type_env = tenv
                            , path_conds = pc
                            , track = EquivTracker et m total finite dcp fname })
                   b@(Bindings { name_gen = ng })
        | E.isSymbolic n eenv
        , Just (dc_symbs, ng') <- arbDC tenv ng t n total = do
            let new_names = map idName $ concat $ map snd dc_symbs
                total' = if n `elem` total
                         then foldr HS.insert total new_names
                         else total
                -- finiteness carries over to sub-expressions too
                finite' = if n `elem` finite
                          then foldr HS.insert finite new_names
                          else finite
                xs = map (\(e, symbs') ->
                                s   { curr_expr = CurrExpr Evaluate e
                                    , expr_env =
                                        foldr E.insertSymbolic
                                              (E.insert n e eenv)
                                              symbs'
                                    , track = EquivTracker et m total' finite' dcp fname
                                    }) dc_symbs
                b' =  b { name_gen = ng' }
                -- only add to total if n was total
                -- not all of these will be used on each branch
                -- they're all fresh, though, so overlap is not a problem
            return (InProgress, zip xs (repeat ()) , b', red)
    redRules red _ s b = return (NoProgress, [(s, ())], b, red)

-- | Build a case expression with one alt for each data constructor of the given type
-- and symbolic arguments.  Thus, the case expression could evaluate to any value of the
-- given type.
arbDC :: TypeEnv
      -> NameGen
      -> Type
      -> Name
      -> HS.HashSet Name
      -> Maybe ([(Expr, [Id])], NameGen)
arbDC tenv ng t n total
    | TyCon tn _:ts <- unTyApp t
    , Just adt <- M.lookup tn tenv =
        let
            dcs = dataCon adt

            bound = boundIds adt
            bound_ts = zip bound ts

            ty_apped_dcs = map (\dc -> mkApp $ Data dc:map Type ts) dcs
            ty_apped_dcs' = (Prim Error TyBottom):ty_apped_dcs
            (ng', dc_symbs) = 
                L.mapAccumL
                    (\ng_ dc ->
                        let
                            anon_ts = anonArgumentTypes dc
                            re_anon = foldr (\(i, t) -> retype i t) anon_ts bound_ts
                            (ars, ng_') = freshIds re_anon ng_
                        in
                        (ng_', (mkApp $ dc:map Var ars, ars))
                    )
                    ng
                    (if trace (show total) $ n `elem` total then ty_apped_dcs else ty_apped_dcs')
        in
        Just (dc_symbs, ng')
    | otherwise = Nothing

-- | Removes and reduces the values in a State's non_red_path_conds field. 
data NonRedPCRed = NonRedPCRed

instance Reducer NonRedPCRed () t where
    initReducer _ _ = ()

    redRules nrpr _  s@(State { expr_env = eenv
                              , curr_expr = cexpr
                              , exec_stack = stck
                              , non_red_path_conds = nr:nrs
                              , model = m })
                      b@(Bindings { higher_order_inst = inst }) = do
        let stck' = Stck.push (CurrExprFrame AddPC cexpr) stck

        let cexpr' = CurrExpr Evaluate nr

        let eenv_si_ces = substHigherOrder eenv m inst cexpr'

        let s' = s { exec_stack = stck'
                   , non_red_path_conds = nrs
                   }
            xs = map (\(eenv', m', ce) -> (s' { expr_env = eenv'
                                              , model = m'
                                              , curr_expr = ce }, ())) eenv_si_ces

        return (InProgress, xs, b, nrpr)
    redRules nrpr _ s b = return (Finished, [(s, ())], b, nrpr)

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
            | (True, bm) <- specializes (typeOf v) (typeOf i) =
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

-- | Removes and reduces the values in a State's non_red_path_conds field by instantiating higher order functions to be constant
data NonRedPCRedConst = NonRedPCRedConst

instance Reducer NonRedPCRedConst () t where
    initReducer _ _ = ()

    redRules nrpr _  s@(State { expr_env = eenv
                              , curr_expr = cexpr
                              , exec_stack = stck
                              , non_red_path_conds = nr:nrs
                              , model = m })
                      b@(Bindings { name_gen = ng
                                  , higher_order_inst = inst }) = do
        let stck' = Stck.push (CurrExprFrame AddPC cexpr) stck

        let cexpr' = CurrExpr Evaluate nr

        let (higher_ord, not_higher_ord) = L.partition (isTyFun . typeOf) $ E.symbolicIds eenv
            (ng', new_lam_is) = L.mapAccumL (\ng_ ts -> swap $ freshIds ts ng_) ng (map anonArgumentTypes higher_ord)
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

        return (InProgress, [(s', ())], b { name_gen = ng'' }, nrpr)
    redRules nrpr _ s b = return (Finished, [(s, ())], b, nrpr)


data TaggerRed = TaggerRed Name NameGen

instance Reducer TaggerRed () t where
    initReducer _ _ = ()

    redRules tr@(TaggerRed n ng) _ s@(State {tags = ts}) b =
        let
            (n'@(Name n_ m_ _ _), ng') = freshSeededName n ng
        in
        if null $ HS.filter (\(Name n__ m__ _ _) -> n_ == n__ && m_ == m__) ts then
            return (Finished, [(s {tags = HS.insert n' ts}, ())], b, TaggerRed n ng')
        else
            return (Finished, [(s, ())], b, tr)


getLogger :: Show t => Config -> Maybe (SomeReducer t)
getLogger config = case logStates config of
                        Log Raw fp -> Just (SomeReducer (Logger fp))
                        Log Pretty fp -> Just (SomeReducer (prettyLogger fp))
                        NoLog -> Nothing

-- | A Reducer to producer logging output 
data Logger = Logger String

instance Show t => Reducer Logger [Int] t where
    initReducer _ _ = []

    redRules l@(Logger fn) li s b = do
        outputState fn li s b pprExecStateStr
        return (NoProgress, [(s, li)], b, l)
    
    updateWithAll _ [(_, l)] = [l]
    updateWithAll _ ss = map (\(l, i) -> l ++ [i]) $ zip (map snd ss) [1..]

-- | A Reducer to producer logging output 
data PrettyLogger = PrettyLogger String PrettyGuide

instance Show t => Reducer PrettyLogger [Int] t where
    initReducer _ s = []

    redRules l@(PrettyLogger fn pg) li s b = do
        let pg' = updatePrettyGuide (s { track = () }) pg
        outputState fn li s b (\s _ -> prettyState pg' s)
        return (NoProgress, [(s, li)], b, PrettyLogger fn pg')
    
    updateWithAll _ [(_, l)] = [l]
    updateWithAll _ ss = map (\(l, i) -> l ++ [i]) $ zip (map snd ss) [1..]

    onAccept _ _ ll = putStrLn $ "Accepted on path " ++ show ll

prettyLogger :: String -> PrettyLogger
prettyLogger s = PrettyLogger s (mkPrettyGuide ())

-- | A Reducer to producer limited logging output.
data LimLogger =
    LimLogger { every_n :: Int -- Output a state every n steps
              , after_n :: Int -- Only begin outputing after passing a certain n
              , down_path :: [Int] -- Output states that have gone down or are going down the given path prefix
              , lim_output_path :: String
              }

data LLTracker = LLTracker { ll_count :: Int, ll_offset :: [Int]}

instance Show t => Reducer LimLogger LLTracker t where
    initReducer ll _ =
        LLTracker { ll_count = every_n ll, ll_offset = []}

    redRules ll@(LimLogger { after_n = aft, down_path = down })
            llt@(LLTracker { ll_count = 0, ll_offset = off }) s b
        | down `L.isPrefixOf` off || off `L.isPrefixOf` down
        , length (rules s) >= aft = do
            outputState (lim_output_path ll) off s b pprExecStateStr
            return (NoProgress, [(s, llt { ll_count = every_n ll })], b, ll)
        | otherwise =
            return (NoProgress, [(s, llt { ll_count = every_n ll })], b, ll)
    redRules ll llt@(LLTracker {ll_count = n}) s b =
        return (NoProgress, [(s, llt { ll_count = n - 1 })], b, ll)
    
    updateWithAll _ [(_, l)] = [l]
    updateWithAll _ ss =
        map (\(llt, i) -> llt { ll_offset = ll_offset llt ++ [i] }) $ zip (map snd ss) [1..]

    onAccept _ _ ll = putStrLn $ "Accepted on path " ++ show (ll_offset ll)


data PredicateLogger = PredicateLogger { pred :: forall t . State t -> Bindings -> Bool
                                       , pred_output_path :: String }

instance Show t => Reducer PredicateLogger [Int] t where
    initReducer ll _ = []

    redRules pl@(PredicateLogger p out) ll s b
        | p s b = do
            outputState out ll s b pprExecStateStr
            return (NoProgress, [(s, ll)], b, pl)
        | otherwise =
            return (NoProgress, [(s, ll)], b, pl)
    
    updateWithAll _ [(_, l)] = [l]
    updateWithAll _ ss = map (\(l, i) -> l ++ [i]) $ zip (map snd ss) [1..]


-- | A Reducer to block states not on a given path 
data OnlyPath = OnlyPath [Int] -- ^ The path to accept

instance Reducer OnlyPath [Int] t where
    initReducer _ _ = []

    redRules ll@(OnlyPath down) off s b
        | down `L.isPrefixOf` off || off `L.isPrefixOf` down =
            return (NoProgress, [(s, off)], b, ll)
        | otherwise = return (Finished, [], b, ll)
    
    updateWithAll _ [(_, l)] = [l]
    updateWithAll _ ss = map (\(llt, i) -> llt ++ [i]) $ zip (map snd ss) [1..]


outputState :: String -> [Int] -> State t -> Bindings -> (State t -> Bindings -> String) -> IO ()
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

-- | Allows executing multiple halters.
-- If the halters disagree, prioritizes the order:
-- Discard, Accept, Switch, Continue
data HCombiner h1 h2 = h1 :<~> h2 deriving (Eq, Show, Read)

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

instance (Halter h1 hv1 t, Halter h2 hv2 t) => Halter (HCombiner h1 h2) (C hv1 hv2) t where
    initHalt (h1 :<~> h2) s =
        let
            hv1 = initHalt h1 s
            hv2 = initHalt h2 s
        in
        C hv1 hv2

    updatePerStateHalt (h1 :<~> h2) (C hv1 hv2) proc s =
        let
            hv1' = updatePerStateHalt h1 hv1 proc s
            hv2' = updatePerStateHalt h2 hv2 proc s
        in
        C hv1' hv2'

    discardOnStart (h1 :<~> h2) (C hv1 hv2) proc s =
        let
            b1 = discardOnStart h1 hv1 proc s
            b2 = discardOnStart h2 hv2 proc s
        in
        b1 || b2

    stopRed (h1 :<~> h2) (C hv1 hv2) proc s = do
        hc1 <- stopRed h1 hv1 proc s
        hc2 <- stopRed h2 hv2 proc s

        return $ min hc1 hc2

    stepHalter (h1 :<~> h2) (C hv1 hv2) proc xs s =
        let
            hv1' = stepHalter h1 hv1 proc xs s
            hv2' = stepHalter h2 hv2 proc xs s
        in
        C hv1' hv2'

    updateHalterWithAll (h1 :<~> h2) shv =
        let
            shv1 = map (\(s, C hv1 _) -> (s, hv1)) shv
            shv2 = map (\(s, C _ hv2) -> (s, hv2)) shv

            shv1' = updateHalterWithAll h1 shv1
            shv2' = updateHalterWithAll h2 shv2
        in
        map (uncurry C) $ zip shv1' shv2'


data  SWHNFHalter = SWHNFHalter

instance Halter SWHNFHalter () t where
    initHalt _ _ = ()
    updatePerStateHalt _ _ _ _ = ()
    stopRed _ _ _ s =
        case isExecValueForm s of
            True -> return Accept
            False -> return Continue
    stepHalter _ _ _ _ _ = ()

-- | Accepts a state when it is in SWHNF and true_assert is true
-- Discards it if in SWHNF and true_assert is false
data AcceptIfViolatedHalter = AcceptIfViolatedHalter

instance Halter AcceptIfViolatedHalter () t where
    initHalt _ _ = ()
    updatePerStateHalt _ _ _ _ = ()
    stopRed _ _ _ s =
        case isExecValueForm s of
            True 
                | true_assert s -> return Accept
                | otherwise -> return Discard
            False -> return Continue
    stepHalter _ _ _ _ _ = ()

-- | Allows execution to continue until the step counter hits 0, then discards the state
data ZeroHalter = ZeroHalter Int

instance Halter ZeroHalter Int t where
    initHalt (ZeroHalter n) _ = n
    updatePerStateHalt _ hv _ _ = hv
    stopRed = halterIsZero
    stepHalter = halterSub1

halterSub1 :: Halter h Int t => h -> Int -> Processed (State t) -> [State t] -> State t -> Int
halterSub1 _ h _ _ _ = h - 1

halterIsZero :: Halter h Int t => h -> Int -> Processed (State t) -> State t -> IO HaltC
halterIsZero _ 0 _ _ = return Discard
halterIsZero _ _ _ _ = return Continue

data MaxOutputsHalter = MaxOutputsHalter (Maybe Int)

instance Halter MaxOutputsHalter (Maybe Int) t where
    initHalt (MaxOutputsHalter m) _ = m
    updatePerStateHalt _ hv _ _ = hv
    stopRed _ m (Processed {accepted = acc}) _ =
        case m of
            Just m' -> return $ if length acc >= m' then Discard else Continue
            _ -> return Continue
    stepHalter _ hv _ _ _ = hv

-- | Switch execution every n steps
data SwitchEveryNHalter = SwitchEveryNHalter Int

instance Halter SwitchEveryNHalter Int t where
    initHalt (SwitchEveryNHalter sw) _ = sw
    updatePerStateHalt (SwitchEveryNHalter sw) _ _ _ = sw
    stopRed _ i pr _ = return $ if i <= 0 then Switch else Continue
    stepHalter _ i _ _ _ = i - 1

    updateHalterWithAll _ [] = []
    updateHalterWithAll _ xs@((_, c):_) =
        let
            len = length xs
            c' = c `quot` len
        in
        replicate len c'

-- | Switches execution every n steps, where n is divided every time
-- a case split happens, by the number of states.
-- That is, if n is 2100, and the case splits into 3 states, each new state will
-- will then get only 700 steps
data BranchAdjSwitchEveryNHalter = BranchAdjSwitchEveryNHalter { switch_def :: Int
                                                               , switch_min :: Int }

data SwitchingPerState = SwitchingPerState { switch_at :: Int -- ^ Max number of steps
                                           , counter :: Int -- ^ Current step counter
                                           }

instance Halter BranchAdjSwitchEveryNHalter SwitchingPerState t where
    initHalt (BranchAdjSwitchEveryNHalter { switch_def = sw }) _ =
        SwitchingPerState { switch_at = sw, counter = sw }
    updatePerStateHalt _ sps@(SwitchingPerState { switch_at = sw }) _ _ =
        sps { counter = sw }
    stopRed _ (SwitchingPerState { counter = i }) _ _ =
        return $ if i <= 0 then Switch else Continue
    stepHalter (BranchAdjSwitchEveryNHalter { switch_min = mi })
               sps@(SwitchingPerState { switch_at = sa, counter = i }) _ xs _ =
        let
            new_sa = max mi (sa `div` length xs)
            new_i = min (i - 1) new_sa
        in
        sps { switch_at = new_sa, counter = new_i}

data BranchAdjVarLookupLimit = BranchAdjVarLookupLimit { var_switch_def :: Int
                                                       , var_switch_min :: Int }

instance Halter BranchAdjVarLookupLimit SwitchingPerState t where
    initHalt (BranchAdjVarLookupLimit { var_switch_def = sw }) _ =
        SwitchingPerState { switch_at = sw, counter = sw }
    updatePerStateHalt _ sps@(SwitchingPerState { switch_at = sw }) _ _ =
        sps { counter = sw }
    stopRed _ (SwitchingPerState { counter = i }) _ _ =
        return $ if i <= 0 then Switch else Continue

    stepHalter (BranchAdjVarLookupLimit { var_switch_min = mi })
               sps@(SwitchingPerState { switch_at = sa, counter = i }) _ xs
               (State { curr_expr = CurrExpr Evaluate (Var _) }) =
        let
            new_sa = max mi (sa `div` length xs)
            new_i = min (i - 1) new_sa
        in
        sps { switch_at = new_sa, counter = new_i}
    stepHalter _ sps _ _ _ = sps


-- Cutoff recursion after n recursive calls
data RecursiveCutOff = RecursiveCutOff Int

instance Halter RecursiveCutOff (HM.HashMap SpannedName Int) t where
    initHalt _ _ = HM.empty
    updatePerStateHalt _ hv _ _ = hv

    stopRed (RecursiveCutOff co) hv _ (State { curr_expr = CurrExpr _ (Var (Id n _)) }) =
        case HM.lookup (SpannedName n) hv of
            Just i
                | i > co -> return Discard
                | otherwise -> return Continue
            Nothing -> return Continue
    stopRed _ _ _ _ = return Continue

    stepHalter _ hv _ _ s@(State { curr_expr = CurrExpr _ (Var (Id n _)) })
        | not $ E.isSymbolic n (expr_env s) =
            case HM.lookup sn hv of
                Just i -> HM.insert sn (i + 1) hv
                Nothing -> HM.insert sn 1 hv
        | otherwise = hv
        where
            sn = SpannedName n
    stepHalter _ hv _ _ _ = hv

-- | If the Name, disregarding the Unique, in the DiscardIfAcceptedTag
-- matches a Tag in the Accepted State list,
-- and in the State being evaluated, discard the State
data DiscardIfAcceptedTag = DiscardIfAcceptedTag Name 

instance Halter DiscardIfAcceptedTag (HS.HashSet Name) t where
    initHalt _ _ = HS.empty
    
    -- updatePerStateHalt gets the intersection of the accepted States Tags,
    -- and the Tags of the State being evaluated.
    -- Then, it filters further by the name in the Halter
    updatePerStateHalt (DiscardIfAcceptedTag (Name n m _ _)) 
                       _ 
                       (Processed {accepted = acc})
                       (State {tags = ts}) =
        let
            allAccTags = HS.unions $ map tags acc
            matchCurrState = HS.intersection ts allAccTags
        in
        HS.filter (\(Name n' m' _ _) -> n == n' && m == m') matchCurrState

    stopRed _ ns _ _ =
        return $ if not (HS.null ns) then Discard else Continue

    stepHalter _ hv _ _ _ = hv

-- | Counts the number of variable lookups are made, and switches the state
-- whenever we've hit a threshold

data VarLookupLimit = VarLookupLimit Int

instance Halter VarLookupLimit Int t where
    initHalt (VarLookupLimit lim) _ = lim
    updatePerStateHalt (VarLookupLimit lim) _ _ _ = lim
    stopRed _ lim _ _ = return $ if lim <= 0 then Switch else Continue

    stepHalter _ lim _ _ (State { curr_expr = CurrExpr Evaluate (Var _) }) = lim - 1
    stepHalter _ lim _ _ _ = lim

data TimerHalter = TimerHalter { init_time :: UTCTime
                               , max_seconds :: NominalDiffTime
                               , if_time_out :: HaltC
                               , check_every :: Int -- ^ How many execution steps to wait before time checks?
                               }

timerHalter :: NominalDiffTime -> IO TimerHalter
timerHalter ms = do
    curr <- getCurrentTime
    return TimerHalter { init_time = curr, max_seconds = ms, if_time_out = Discard, check_every = 10 }

instance Halter TimerHalter Int t where
    initHalt _ _ = 0
    updatePerStateHalt _ _ _ _ = 0

    stopRed tr@(TimerHalter { init_time = it
                            , max_seconds = ms
                            , if_time_out = def })
            v (Processed { accepted = acc }) s
        | v == 0
        , not (null acc) = do
            curr <- getCurrentTime
            let diff = diffUTCTime curr it

            if diff > ms
                then return def
                else return Continue
        | otherwise = return Continue

    stepHalter (TimerHalter { check_every = ce }) v _ _ _
        | v >= ce = 0
        | otherwise = v + 1


-- | Runs the halter only if some predicate held on the processed and current state,
-- when the current state was switched to.
-- Otherwise, just allows execution to continue 
data OnlyIf h = OnlyIf { run_only_if :: forall t . Processed (State t) -> State t -> Bool
                       , below :: h }

data OnlyIfHV hv = OnlyIfHV { pred_holds :: Bool, below_hv :: hv }

instance Halter h hv t => Halter (OnlyIf h) (OnlyIfHV hv) t where
    initHalt h s = OnlyIfHV (run_only_if h (Processed [] []) s) $ initHalt (below h) s
    updatePerStateHalt h (OnlyIfHV holds hv) pr s =
        let
            holds' = run_only_if h pr s
            hv' = updatePerStateHalt (below h) hv pr s
        in
        OnlyIfHV holds' hv'
    
    discardOnStart h (OnlyIfHV holds hv) pr s
        | holds = discardOnStart (below h) hv pr s
        | otherwise = False
    
    stopRed h (OnlyIfHV holds hv) pr s
        | holds = stopRed (below h) hv pr s
        | otherwise = return Continue

    stepHalter h (OnlyIfHV holds hv) pr xs s =
        let
            hv' = stepHalter (below h) hv pr xs s
        in
        OnlyIfHV holds hv'

-- Orderer things

-- | Does not respect getState, but simply uses the default Ord instance
data OCombiner o1 o2 = o1 :<-> o2 deriving (Eq, Show, Read)

instance (MinOrderer or1 sov1 b1 t, MinOrderer or2 sov2 b2 t)
      => MinOrderer (OCombiner or1 or2) (C sov1 sov2) (b1, b2) t where
  
    -- | Initializing the per state ordering value 
    minInitPerStateOrder (or1 :<-> or2) s =
      let
          sov1 = minInitPerStateOrder or1 s
          sov2 = minInitPerStateOrder or2 s
      in
      C sov1 sov2

    -- | Assigns each state some value of an ordered type, and then proceeds with execution on the
    -- state assigned the minimal value
    minOrderStates (or1 :<-> or2) (C sov1 sov2) pr s =
      let
          (sov1', or1') = minOrderStates or1 sov1 pr s
          (sov2', or2') = minOrderStates or2 sov2 pr s
      in
      ((sov1', sov2'), or1' :<-> or2')

    -- | Run on the selected state, to update it's sov field
    minUpdateSelected (or1 :<-> or2) (C sov1 sov2) proc s = 
      let
          sov1' = minUpdateSelected or1 sov1 proc s
          sov2' = minUpdateSelected or2 sov2 proc s
      in
      C sov1' sov2'

    minStepOrderer (or1 :<-> or2) (C sov1 sov2) proc xs s =
        let
            sov1' = minStepOrderer or1 sov1 proc xs s
            sov2' = minStepOrderer or2 sov2 proc xs s
        in
        C sov1' sov2'

data FlexOrdCombiner v1 v2 v3 or1 or2 = OrdComb (v1 -> v2 -> v3) or1 or2

instance (MinOrderer or1 sov1 v1 t, MinOrderer or2 sov2 v2 t, Ord v3)
      => MinOrderer (FlexOrdCombiner v1 v2 v3 or1 or2) (C sov1 sov2) v3 t where

    -- | Initializing the per state ordering value 
    minInitPerStateOrder (OrdComb _ or1 or2) s =
      let
          sov1 = minInitPerStateOrder or1 s
          sov2 = minInitPerStateOrder or2 s
      in
      C sov1 sov2

    -- | Assigns each state some value of an ordered type, and then proceeds with execution on the
    -- state assigned the minimal value
    minOrderStates (OrdComb f or1 or2) (C sov1 sov2) pr s =
      let
          (sov1', or1') = minOrderStates or1 sov1 pr s
          (sov2', or2') = minOrderStates or2 sov2 pr s
      in
      (f sov1' sov2', OrdComb f or1' or2')

    -- | Run on the selected state, to update it's sov field
    minUpdateSelected (OrdComb _ or1 or2) (C sov1 sov2) proc s = 
      let
          sov1' = minUpdateSelected or1 sov1 proc s
          sov2' = minUpdateSelected or2 sov2 proc s
      in
      C sov1' sov2'

    minStepOrderer (OrdComb _ or1 or2) (C sov1 sov2) proc xs s =
        let
            sov1' = minStepOrderer or1 sov1 proc xs s
            sov2' = minStepOrderer or2 sov2 proc xs s
        in
        C sov1' sov2'

data NextOrderer = NextOrderer

instance Orderer NextOrderer () Int t where
    initPerStateOrder _ _ = ()
    orderStates or _ _ _ = (0, or)
    updateSelected _ v _ _ = v

-- | Continue execution on the state that has been picked the least in the past. 
data PickLeastUsedOrderer = PickLeastUsedOrderer

instance Orderer PickLeastUsedOrderer Int Int t where
    initPerStateOrder _ _ = 0
    orderStates or v _ _ = (v, or)
    updateSelected _ v _ _ = v + 1

-- | Floors and does bucket size
data BucketSizeOrderer = BucketSizeOrderer Int

instance MinOrderer BucketSizeOrderer Int Int t where
    minInitPerStateOrder _ _ = 0

    minOrderStates ord@(BucketSizeOrderer b) v _ _ = (floor (fromIntegral v / fromIntegral b :: Float), ord)

    minUpdateSelected _ v _ _ = v + 1

-- | Order by the number of PCs
data CaseCountOrderer = CaseCountOrderer

instance Orderer CaseCountOrderer Int Int t where
    initPerStateOrder _ _ = 0

    orderStates or v _ _ = (v, or)

    updateSelected _ v _ _ = v

    stepOrderer _ v _ _ (State { curr_expr = CurrExpr _ (Case _ _ _) }) = v + 1
    stepOrderer _ v _ _ _ = v


-- Orders by the smallest symbolic ADTs
data SymbolicADTOrderer = SymbolicADTOrderer

instance Orderer SymbolicADTOrderer (HS.HashSet Name) Int t where
    initPerStateOrder _ = HS.fromList . map idName . E.symbolicIds . expr_env
    orderStates or v _ _ = (HS.size v, or)

    updateSelected _ v _ _ = v

    stepOrderer _ v _ _ s =
        v `HS.union` (HS.fromList . map idName . E.symbolicIds . expr_env $ s)

-- Orders by the size (in terms of height) of (previously) symbolic ADT.
-- In particular, aims to first execute those states with a height closest to
-- the specified height.
data ADTHeightOrderer = ADTHeightOrderer
                            Int -- ^ What height should we prioritize?
                            (Maybe Name) -- ^ If we see a tick with the specified Name, add it to the set

-- Normally, each state tracks the names of currently symbolic variables,
-- but here we want all variables that were ever symbolic.
-- To track this, we use a HashSet.
-- The tracked bool is to speed up adjusting this hashset- if it is set to false,
-- we do not update the hashset.  If it is set to true,
-- after the next step the hashset will be updated, and the bool will be set
-- back to false.
-- This avoids repeated operations on the hashset after rules that we know
-- will not add symbolic variables.
instance MinOrderer ADTHeightOrderer (HS.HashSet Name, Bool) Int t where
    minInitPerStateOrder _ s = (HS.fromList . map idName . E.symbolicIds . expr_env $ s, False)
    minOrderStates ord@(ADTHeightOrderer pref_height _) (v, _) _ s =
        let
            m = maximum $ (-1):(HS.toList $ HS.map (flip adtHeight s) v)
            h = abs (pref_height - m)
        in
        (h, ord)
    minUpdateSelected _ v _ _ = v

    minStepOrderer _ (v, _) _ _
                  (State { curr_expr = CurrExpr _ (SymGen _) }) = (v, True)
    minStepOrderer _ (v, True) _ _ s =
        (v `HS.union` (HS.fromList . map idName . E.symbolicIds . expr_env $ s), False)
    minStepOrderer (ADTHeightOrderer _ (Just n)) (v, _) _ _ 
                   s@(State { curr_expr = CurrExpr _ (Tick (NamedLoc n') (Var (Id vn _))) }) 
            | n == n' =
                (HS.insert vn v, False)
    minStepOrderer _ v _ _ s =
        v

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

-- Orders by the combined size of (previously) symbolic ADT.
-- In particular, aims to first execute those states with a combined ADT size closest to
-- the specified zize.
data ADTSizeOrderer = ADTSizeOrderer
                            Int -- ^ What size should we prioritize?
                            (Maybe Name) -- ^ If we see a tick with the specified Name, add it to the set

-- Normally, each state tracks the names of currently symbolic variables,
-- but here we want all variables that were ever symbolic.
-- To track this, we use a HashSet.
-- The tracked bool is to speed up adjusting this hashset- if it is set to false,
-- we do not update the hashset.  If it is set to true,
-- after the next step the hashset will be updated, and the bool will be set
-- back to false.
-- This avoids repeated operations on the hashset after rules that we know
-- will not add symbolic variables.
instance MinOrderer ADTSizeOrderer (HS.HashSet Name, Bool) Int t where
    minInitPerStateOrder _ s = (HS.fromList . map idName . E.symbolicIds . expr_env $ s, False)
    minOrderStates ord@(ADTSizeOrderer pref_height _) (v, _) _ s =
        let
            m = sum (HS.toList $ HS.map (flip adtSize s) v)
            h = abs (pref_height - m)
        in
        (h, ord)
    minUpdateSelected _ v _ _ = v

    minStepOrderer _ (v, _) _ _
                  (State { curr_expr = CurrExpr _ (SymGen _) }) = (v, True)
    minStepOrderer _ (v, True) _ _ s =
        (v `HS.union` (HS.fromList . map idName . E.symbolicIds . expr_env $ s), False)
    minStepOrderer (ADTSizeOrderer _ (Just n)) (v, _) _ _ 
                   s@(State { curr_expr = CurrExpr _ (Tick (NamedLoc n') (Var (Id vn _))) }) 
            | n == n' =
                (HS.insert vn v, False)
    minStepOrderer _ v _ _ s =
        v

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


-- Orders by the number of Path Constraints
data PCSizeOrderer = PCSizeOrderer
                            Int -- ^ What size should we prioritize?

-- The tracked bool is to speed up adjusting this hashset- if it is set to false,
-- we do not update the hashset.  If it is set to true,
-- after the next step the hashset will be updated, and the bool will be set
-- back to false.
-- This avoids repeated operations on the hashset after rules that we know
-- will not add symbolic variables.
instance MinOrderer PCSizeOrderer () Int t where
    minInitPerStateOrder _ s = ()
    minOrderStates ord@(PCSizeOrderer pref_height) _ _ s =
        let
            m = PC.number (path_conds s)
            h = abs (pref_height - m)
        in
        (h, ord)
    minUpdateSelected _ v _ _ = v

    minStepOrderer _ d _ _ _ = d

data RandomOrderer = RandomOrderer StdGen

instance MinOrderer RandomOrderer () Int t where
    minInitPerStateOrder _ _ = ()

    minOrderStates (RandomOrderer gen) _ _ _ =
        let
            (v, gen') = randomR (0, 1000) gen
        in
        (v, RandomOrderer gen')

    minUpdateSelected _ v _ _ = v

mkRandomOrderer :: Int -> RandomOrderer
mkRandomOrderer = RandomOrderer . mkStdGen

getRandomOrderer :: IO RandomOrderer
getRandomOrderer = return . RandomOrderer =<< getStdGen

type WeightFunction t = Processed (State t) -> State t -> Int -> Int

data WeightedRandomOrderer t =
    WeightedRandomOrderer (WeightFunction t) StdGen

instance Orderer (WeightedRandomOrderer t) () Int t where
    initPerStateOrder _ _ = ()

    orderStates (WeightedRandomOrderer f gen) _ pr s =
        let
            (v, gen') = randomR (0, 1000) gen
        in
        (f pr s v, WeightedRandomOrderer f gen')

    updateSelected _ v _ _ = v

mkWeightedRandomOrderer :: WeightFunction t -> Int -> WeightedRandomOrderer t
mkWeightedRandomOrderer f = WeightedRandomOrderer f . mkStdGen

getWeightedRandomOrderer :: WeightFunction t -> IO (WeightedRandomOrderer t)
getWeightedRandomOrderer f = return . WeightedRandomOrderer f =<< getStdGen

-- Wraps an existing Orderer, and increases it's value by 1, every time
-- it doesn't change after N steps 
data IncrAfterN ord = IncrAfterN Int ord

data IncrAfterNTr sov = IncrAfterNTr { steps_since_change :: Int
                                     , incr_by :: Int
                                     , underlying :: sov }

instance (Eq sov, Enum b, MinOrderer ord sov b t) => MinOrderer (IncrAfterN ord) (IncrAfterNTr sov) b t where
    minInitPerStateOrder (IncrAfterN _ ord) s =
        IncrAfterNTr { steps_since_change = 0
                     , incr_by = 0
                     , underlying = minInitPerStateOrder ord s }
    minOrderStates (IncrAfterN n ord) sov pr s =
        let
            (b, ord') = minOrderStates ord (underlying sov) pr s
        in
        (succNTimes (incr_by sov) b, IncrAfterN n ord')
    minUpdateSelected (IncrAfterN _ ord) sov pr s =
        sov { underlying = minUpdateSelected ord (underlying sov) pr s }
    minStepOrderer (IncrAfterN ma ord) sov pr xs s
        | steps_since_change sov >= ma =
            sov' { incr_by = incr_by sov' + 1
                 , steps_since_change = 0 }
        | under /= under' =
            sov' { steps_since_change = 0 }
        | otherwise =
            sov' { steps_since_change = steps_since_change sov' + 1}
        where
            under = underlying sov
            under' = minStepOrderer ord under pr xs s
            sov' = sov { underlying = under' }


succNTimes :: Enum b => Int -> b -> b
succNTimes x b
    | x <= 0 = b
    | otherwise = succNTimes (x - 1) (succ b)

-- Wraps an existing orderer, and divides its value by 2 if true_assert is true
data QuotTrueAssert ord = QuotTrueAssert ord

instance (Integral b, MinOrderer ord sov b t) => MinOrderer (QuotTrueAssert ord) sov b t where
    minInitPerStateOrder (QuotTrueAssert ord) = minInitPerStateOrder ord
    minOrderStates (QuotTrueAssert ord) sov pr s =
        let
            (b, ord') = minOrderStates ord sov pr s
        in
        (if true_assert s then b `quot` 2 else b, QuotTrueAssert ord')
    minUpdateSelected (QuotTrueAssert ord) = minUpdateSelected ord
    minStepOrderer (QuotTrueAssert ord) = minStepOrderer ord 

--------
--------

-- | Uses a passed Reducer, Halter and Orderer to execute the reduce on the State, and generated States
runReducer :: (Reducer r rv t, Halter h hv t, Orderer or sov b t) => r -> h -> or -> State t -> Bindings -> IO (Processed (State t), Bindings)
runReducer red hal ord s b = do
    let pr = Processed {accepted = [], discarded = []}
    let s' = ExState { state = s
                     , reducer_val = initReducer red s
                     , halter_val = initHalt hal s
                     , order_val = initPerStateOrder ord s }

    (states, b') <- runReducer' red hal ord pr s' b M.empty
    return (states, b')

runReducer' :: (Reducer r rv t, Halter h hv t, Orderer or sov b t) 
            => r 
            -> h 
            -> or 
            -> Processed (State t) 
            -> ExState rv hv sov t 
            -> Bindings
            -> M.Map b [ExState rv hv sov t] 
            -> IO (Processed (State t), Bindings)
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
                        -- runReducer' red hal ord pr' (updateExStateHalter hal pr' rs') b xs'
                    Nothing -> return (pr', b)
            | hc == Discard ->
                let
                    pr' = pr {discarded = state rs:discarded pr}
                    jrs = minState ord pr' xs
                in
                case jrs of
                    Just (rs', xs') ->
                        switchState red hal ord pr' rs' b xs'
                        -- runReducer' red hal ord pr' (updateExStateHalter hal pr' rs') b xs'
                    Nothing -> return (pr', b)
            | hc == Switch ->
                let
                    (k, ord') = orderStates ord (order_val rs') pr (state rs)
                    rs' = rs { order_val = updateSelected ord (order_val rs) pr (state rs) }

                    Just (rs'', xs') = minState ord pr (M.insertWith (++) k [rs'] xs)
                in
                switchState red hal ord' pr rs'' b xs'
                -- if not $ discardOnStart hal (halter_val rs''') pr (state rs''')
                --     then runReducer' red hal ord pr rs''' b xs'
                --     else runReducerList red hal ord (pr {discarded = rs''':discarded pr}) xs' b
            | otherwise -> do
                (_, reduceds, b', red') <- redRules red r_val s b
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
                            (ord', b_ss_tail) =
                                L.mapAccumR (\e_ord s' ->
                                    let
                                        (n_b, n_ord) = orderStates e_ord (order_val s') pr (state s')
                                    in
                                    (n_ord, (n_b, s'))) ord ss_tail

                            xs' = foldr (\(or_b, s') -> M.insertWith (++) or_b [s']) xs b_ss_tail

                        runReducer' red' hal ord' pr s_h b' xs'
                    [] -> runReducerList red' hal ord pr xs b' 

switchState :: (Reducer r rv t, Halter h hv t, Orderer or sov b t)
            => r
            -> h
            -> or
            -> Processed (State t) 
            -> ExState rv hv sov t 
            -> Bindings
            -> M.Map b [ExState rv hv sov t] 
            -> IO (Processed (State t), Bindings)
switchState red hal ord  pr rs b xs
    | not $ discardOnStart hal (halter_val rs') pr (state rs') =
        runReducer' red hal ord pr rs' b xs
    | otherwise =
        runReducerListSwitching red hal ord (pr {discarded = state rs':discarded pr}) xs b
    where
        rs' = rs { halter_val = updatePerStateHalt hal (halter_val rs) pr (state rs) }

-- To be used when we we need to select a state without switching 
runReducerList :: (Reducer r rv t, Halter h hv t, Orderer or sov b t) 
               => r 
               -> h 
               -> or 
               -> Processed (State t)
               -> M.Map b [ExState rv hv sov t]
               -> Bindings
               -> IO (Processed (State t), Bindings)
runReducerList red hal ord pr m binds =
    case minState ord pr m of
        Just (rs, m') ->
            let
                rs' = rs { halter_val = updatePerStateHalt hal (halter_val rs) pr (state rs) }
            in
            runReducer' red hal ord pr rs' binds m'
        Nothing -> return (pr, binds)

-- To be used when we are possibly switching states 
runReducerListSwitching :: (Reducer r rv t, Halter h hv t, Orderer or sov b t) 
                        => r 
                        -> h 
                        -> or 
                        -> Processed (State t)
                        -> M.Map b [ExState rv hv sov t]
                        -> Bindings
                        -> IO (Processed (State t), Bindings)
runReducerListSwitching red hal ord pr m binds =
    case minState ord pr m of
        Just (x, m') -> switchState red hal ord pr x binds m'
        Nothing -> return (pr, binds)

processedToState :: Processed (ExState rv hv sov t) -> Processed (State t)
processedToState (Processed {accepted = app, discarded = dis}) =
    Processed {accepted = map state app, discarded = map state dis}

-- Uses the Orderer to determine which state to continue execution on.
-- Returns that State, and a list of the rest of the states 
minState :: (Orderer or sov b t)
         => or
         -> Processed (State t)
         -> M.Map b [ExState rv hv sov t]
         -> Maybe ((ExState rv hv sov t), M.Map b [ExState rv hv sov t])
minState ord pr m =
    case getState ord pr m of
      Just (k, x:[]) -> Just (x, M.delete k m)
      Just (k, x:xs) -> Just (x, M.insert k xs m)
      Just (k, []) -> minState ord pr $ M.delete k m
      Nothing -> Nothing


numStates :: M.Map b [ExState rv hv sov t] -> Int
numStates = sum . map length . M.elems
