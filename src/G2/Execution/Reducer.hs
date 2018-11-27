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

                                      , Processed (..)
                                      , ReducerRes (..)
                                      , HaltC (..)

                                      , SomeReducer (..)
                                      , SomeHalter (..)
                                      , SomeOrderer (..)

                                      -- Reducers
                                      , RCombiner (..)
                                      , StdRed (..)
                                      , NonRedPCRed (..)
                                      , TaggerRed (..)

                                      -- Halters
                                      , AcceptHalter (..)
                                      , HCombiner (..)
                                      , ZeroHalter (..)
                                      , DiscardIfAcceptedTag (..)
                                      , MaxOutputsHalter (..)
                                      , SwitchEveryNHalter (..)

                                      -- Orderers
                                      , NextOrderer (..)
                                      , PickLeastUsedOrderer (..)

                                      , halterSub1
                                      , halterIsZero

                                      , reduce
                                      , runReducer ) where

import qualified G2.Language.ApplyTypes as AT
import qualified G2.Language.ExprEnv as E
import G2.Config
import G2.Execution.Rules
import G2.Language
import G2.Language.Stack as Stck
import G2.Solver
import G2.Lib.Printers

import Data.Foldable
import qualified Data.HashSet as S
import qualified Data.Map as M
import System.Directory

-- | Used when applying execution rules
-- Allows tracking extra information to control halting of rule application,
-- and to reorder states
-- see also, the Reducer, Halter, Orderer typeclasses
-- cases is used for logging states
data ExState hv sov t = ExState { state :: State t
                                , halter_val :: hv
                                , order_val :: sov
                                , cases :: [Int]
                                 }

-- | Keeps track of type a's that have either been accepted or dropped
data Processed a = Processed { accepted :: [a]
                             , discarded :: [a] }

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
class Reducer r t where
    -- | redRules
    -- Takes a State, and performs the appropriate Reduction Rule
    redRules :: r -> State t -> IO (ReducerRes, [State t], r)

-- | Determines when to stop evaluating a state
-- The type parameter h is used to disambiguate between different producers.
-- To create a new Halter, define some new type, and use it as h.
class Halter h hv t | h -> hv where
    -- | Initializes each state halter value
    initHalt :: h -> Config -> State t -> hv

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
    stopRed :: h -> hv -> Processed (State t) -> State t -> HaltC

    -- | Takes a state, and updates it's halter record field
    stepHalter :: h -> hv -> Processed (State t) -> State t -> hv

-- | Picks an order to evaluate the states, to allow prioritizing some over others 
-- The type parameter or is used to disambiguate between different producers.
-- To create a new reducer, define some new type, and use it as or.
class Ord b => Orderer or sov b t | or -> sov, or -> b where
    -- | Initializing the per state ordering value 
    initPerStateOrder :: or -> Config -> State t -> sov

    -- | Assigns each state some value of an ordered type, and then proceeds with execution on the
    -- state assigned the minimal value
    orderStates :: or -> sov -> State t -> b

    -- | Run on the selected state, to update it's sov field
    updateSelected :: or -> sov -> Processed (State t) -> State t -> sov

data SomeReducer t where
    SomeReducer :: forall r t . Reducer r t => r -> SomeReducer t

data SomeHalter t where
    SomeHalter :: forall h hv t . Halter h hv t => h -> SomeHalter t

data SomeOrderer t where
    SomeOrderer :: forall or sov b t . Orderer or sov b t => or -> SomeOrderer t

-- | Combines reducers in various ways
data RCombiner r1 r2 = r1 :<~ r2 -- ^ Apply r2, followed by r1.  Takes the leftmost update to r1
                     | r1 :<~? r2 -- ^ Apply r2, apply r1 only if r2 returns NoProgress
                     | r1 :<~| r2 -- ^ Apply r2, apply r1 only if r2 returns Finished
                     deriving (Eq, Show, Read)

instance (Reducer r1 t, Reducer r2 t) => Reducer (RCombiner r1 r2) t where
    redRules (r1 :<~ r2) s = do
        (rr2, s', r2') <- redRules r2 s
        (rr1, s'', r1') <- redRulesToStates r1 s'

        return (progPrioritizer rr1 rr2, s'', r1' :<~ r2')
    redRules (r1 :<~? r2) s = do
        (rr2, s', r2') <- redRules r2 s
        case rr2 of
            NoProgress -> do
                (rr1, s'', r1') <- redRulesToStates r1 s'
                return (rr1, s'', r1' :<~? r2')
            _ -> return (rr2, s', r1 :<~? r2')
    redRules (r1 :<~| r2) s = do
        (rr2, s', r2') <- redRules r2 s
        case rr2 of
            Finished -> do
                (rr1, s'', r1') <- redRulesToStates r1 s'
                return (rr1, s'', r1' :<~| r2')
            _ -> return (rr2, s', r1 :<~| r2')

redRulesToStates :: Reducer r t => r -> [State t] -> IO (ReducerRes, [State t], r)
redRulesToStates r s = do
    rs <- mapM (redRules r) s
    let (rr, s', r') = unzip3 rs

    let rf = foldr progPrioritizer NoProgress rr

    return $ (rf, concat s', head r')

data StdRed con = StdRed con Config

instance Solver con => Reducer (StdRed con) () where
    redRules stdr@(StdRed solver config) s = do
        (r, s') <- reduce (stdReduce config) solver config s
        
        return (if r == RuleIdentity then Finished else InProgress, s', stdr)

-- | Removes and reduces the values in a State's non_red_path_conds field. 
data NonRedPCRed = NonRedPCRed Config

instance Reducer NonRedPCRed t where
    redRules nrpr s@(State { expr_env = eenv
                           , curr_expr = cexpr
                           , exec_stack = stck
                           , path_conds = pc
                           , non_red_path_conds = nr:nrs
                           , apply_types = at
                           , input_ids = is
                           , symbolic_ids = si }) = do
        let stck' = Stck.push (CurrExprFrame cexpr) stck

        let cexpr' = CurrExpr Evaluate nr
        let cexpr'' = higherOrderToAppTys eenv at cexpr'

        let s' = s { curr_expr = cexpr''
                   , exec_stack = stck'
                   , non_red_path_conds = nrs
                   , path_conds = AT.typeToAppType at pc
                   , input_ids = AT.typeToAppType at is
                   , symbolic_ids = AT.typeToAppType at si }

        return (InProgress, [s'], nrpr)
    redRules nrpr s = return (Finished, [s], nrpr)

higherOrderToAppTys :: ASTContainer m Expr => ExprEnv -> ApplyTypes -> m -> m
higherOrderToAppTys eenv at = modifyASTs (higherOrderToAppTys' eenv at)

higherOrderToAppTys' :: ExprEnv -> ApplyTypes -> Expr -> Expr
higherOrderToAppTys' eenv at v@(Var (Id n t))
    | E.isSymbolic n eenv
    , isTyFun t
    , Just (tn, f) <- AT.lookup t at =
        App (Var f) (Var (Id n (TyCon tn TYPE)))
    | otherwise = v
higherOrderToAppTys' _ _ e = e

data TaggerRed = TaggerRed Name NameGen

instance Reducer TaggerRed t where
    redRules tr@(TaggerRed n ng) s@(State {tags = ts}) =
        let
            (n'@(Name n_ m_ _ _), ng') = freshSeededName n ng
        in
        if null $ S.filter (\(Name n__ m__ _ _) -> n_ == n__ && m_ == m__) ts then
            return (Finished, [s {tags = S.insert n' ts}], TaggerRed n ng')
        else
            return (Finished, [s], tr)

-- | Allows executing multiple halters.
-- If the halters disagree, prioritizes the order:
-- Discard, Accept, Switch, Continue
data HCombiner h1 h2 = h1 :<~> h2 deriving (Eq, Show, Read)

-- We use C to combine the halter values for HCombiner
-- We should never define any other instance of Halter with C, or export it
-- because this could lead to undecidable instances
data C a b = C a b

instance (ASTContainer a Expr, ASTContainer b Expr) => ASTContainer (C a b) Expr where
    containedASTs (C a b) = containedASTs a ++ containedASTs b
    modifyContainedASTs f (C a b) = C (modifyContainedASTs f a) (modifyContainedASTs f b)

instance (ASTContainer a Type, ASTContainer b Type) => ASTContainer (C a b) Type where
    containedASTs (C a b) = containedASTs a ++ containedASTs b
    modifyContainedASTs f (C a b) = C (modifyContainedASTs f a) (modifyContainedASTs f b)

instance (Named a, Named b) => Named (C a b) where
    names (C a b) = names a ++ names b
    rename old new (C a b) = C (rename old new a) (rename old new b)
    renames hm (C a b) = C (renames hm a) (renames hm b)

instance (Halter h1 hv1 t, Halter h2 hv2 t) => Halter (HCombiner h1 h2) (C hv1 hv2) t where
    initHalt (h1 :<~> h2) config s =
        let
            hv1 = initHalt h1 config s
            hv2 = initHalt h2 config s
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

    stopRed (h1 :<~> h2) (C hv1 hv2) proc s =
        let
            hc1 = stopRed h1 hv1 proc s
            hc2 = stopRed h2 hv2 proc s
        in
        min hc1 hc2

    stepHalter (h1 :<~> h2) (C hv1 hv2) proc s =
        let
            hv1' = stepHalter h1 hv1 proc s
            hv2' = stepHalter h2 hv2 proc s
        in
        C hv1' hv2'

-- | Accepts a state when it is in ExecNormalForm
data AcceptHalter = AcceptHalter

instance Halter AcceptHalter () t where
    initHalt _ _ _ = ()
    updatePerStateHalt _ _ _ _ = ()
    stopRed _ _ _ s =
        case isExecValueForm s && true_assert s of
            True -> Accept
            False -> Continue
    stepHalter _ _ _ _ = ()

-- | Allows execution to continue until the step counter hits 0, then discards the state
data ZeroHalter = ZeroHalter

instance Halter ZeroHalter Int t where
    initHalt _ config _ = steps config
    updatePerStateHalt _ hv _ _ = hv
    stopRed = halterIsZero
    stepHalter = halterSub1

data MaxOutputsHalter = MaxOutputsHalter

instance Halter MaxOutputsHalter (Maybe Int) t where
    initHalt _ config _ = maxOutputs config
    updatePerStateHalt _ hv _ _ = hv
    stopRed _ m (Processed {accepted = acc}) _ =
        case m of
            Just m' -> if length acc >= m' then Discard else Continue
            _ -> Continue
    stepHalter _ hv _ _ = hv

-- | Switch execution every n steps
data SwitchEveryNHalter = SwitchEveryNHalter Int

instance Halter SwitchEveryNHalter Int t where
    initHalt (SwitchEveryNHalter sw) _ _ = sw
    updatePerStateHalt (SwitchEveryNHalter sw) _ _ _ = sw
    stopRed _ i _ _ = if i <= 0 then Switch else Continue
    stepHalter _ i _ _ = i - 1

-- | If the Name, disregarding the Unique, in the DiscardIfAcceptedTag
-- matches a Tag in the Accepted State list,
-- and in the State being evaluated, discard the State
data DiscardIfAcceptedTag = DiscardIfAcceptedTag Name 

instance Halter DiscardIfAcceptedTag (S.HashSet Name) t where
    initHalt _ _ _ = S.empty
    
    -- updatePerStateHalt gets the intersection of the accepted States Tags,
    -- and the Tags of the State being evaluated.
    -- Then, it filters further by the name in the Halter
    updatePerStateHalt (DiscardIfAcceptedTag (Name n m _ _)) 
                       _ 
                       (Processed {accepted = acc})
                       (State {tags = ts}) =
        let
            allAccTags = S.unions $ map tags acc
            matchCurrState = S.intersection ts allAccTags
        in
        S.filter (\(Name n' m' _ _) -> n == n' && m == m') matchCurrState

    stopRed _ ns _ _ =
        if not (S.null ns) then Discard else Continue

    stepHalter _ hv _ _ = hv

data NextOrderer = NextOrderer

instance Orderer NextOrderer () Int t where
    initPerStateOrder _ _ _ = ()
    orderStates _ _ _ = 0
    updateSelected _ v _ _ = v

-- | Continue execution on the state that has been picked the least in the past. 
data PickLeastUsedOrderer = PickLeastUsedOrderer

instance Orderer PickLeastUsedOrderer Int Int t where
    initPerStateOrder _ _ _ = 0
    orderStates _ v _ = v
    updateSelected _ v _ _ = v + 1

halterSub1 :: Halter h Int t => h -> Int -> Processed (State t) -> State t -> Int
halterSub1 _ h _ _ = h - 1

halterIsZero :: Halter h Int t => h -> Int -> Processed (State t) -> State t -> HaltC
halterIsZero _ 0 _ _ = Discard
halterIsZero _ _ _ _ = Continue

--------
--------

reduce :: Solver solver => (State t -> (Rule, [ReduceResult t])) -> solver -> Config -> State t -> IO (Rule, [State t])
reduce red con config s = do
    let (rule, res) = red s
    sts <- resultsToState con config rule s res
    return (rule, sts)

-- | Uses a passed Reducer, Halter and Orderer to execute the reduce on the State, and generated States
runReducer :: (Reducer r t, Halter h hv t, Orderer or sov b t) => r -> h -> or -> Config -> State t -> IO [([Int], State t)]
runReducer red hal ord config s =
    let
        pr = Processed {accepted = [], discarded = []}
        s' = ExState { state = s
                     , halter_val = initHalt hal config s
                     , order_val = initPerStateOrder ord config s
                     , cases = []}
    in
     mapM (\ExState {state = st, cases = c} -> return (c, st)) =<< runReducer' red hal ord config pr s' M.empty 

runReducer' :: (Reducer r t, Halter h hv t, Orderer or sov b t) => r -> h -> or -> Config -> Processed (ExState hv sov t) -> ExState hv sov t -> M.Map b [ExState hv sov t] -> IO [ExState hv sov t]
runReducer' red hal ord config pr rs@(ExState { state = s, halter_val = h_val, cases = is }) xs
    | hc == Accept =
        let
            pr' = pr {accepted = rs:accepted pr}
            jrs = minState xs
        in
        case jrs of
            Just (rs', xs') -> return . (:) rs =<< runReducer' red hal ord config pr' (updateExStateHalter hal pr' rs') xs'
            Nothing -> return [rs]
    | hc == Discard =
        let
            pr' = pr {discarded = rs:discarded pr}
            jrs = minState xs
        in
        case jrs of
            Just (rs', xs') -> runReducer' red hal ord config pr' (updateExStateHalter hal pr' rs') xs'
            Nothing -> return []
    | hc == Switch =
        let
            k = orderStates ord (order_val rs') (state rs)
            rs' = rs { order_val = updateSelected ord (order_val rs) ps (state rs) }

            Just (rs'', xs') = minState (M.insertWith (++) k [rs'] xs)
            
            rs''' = rs'' { halter_val = updatePerStateHalt hal (halter_val rs'') ps (state rs'') }
        in
        if not $ discardOnStart hal (halter_val rs''') ps (state rs''')
            then runReducer' red hal ord config pr rs''' xs'
            else runReducerList red hal ord config (pr {discarded = rs''':discarded pr}) xs'
    | otherwise = do
        case logStates config of
            Just f -> outputState f is s
            Nothing -> return ()

        (_, reduceds, red') <- redRules red s
        let reduceds' = map (\r -> r {num_steps = num_steps r + 1}) reduceds

        let isred = if length (reduceds') > 1 then zip (map Just [1..]) reduceds' else zip (repeat Nothing) reduceds'
        
        let mod_info = map (\(i, s') -> rs { state = s'
                                           , halter_val = stepHalter hal h_val ps s'
                                           , cases = is ++ maybe [] (\i' -> [i']) i}) isred
        
        let xs' = foldr (\s' -> M.insertWith (++) (orderStates ord (order_val s') (state s')) [s']) xs mod_info

        runReducerList red' hal ord config pr xs'
    where
        hc = stopRed hal h_val ps s
        ps = processedToState pr

runReducerList :: (Reducer r t, Halter h hv t, Orderer or sov b t) => r -> h -> or -> Config -> Processed (ExState hv sov t) -> M.Map b [ExState hv sov t] -> IO [ExState hv sov t]
runReducerList red hal ord config pr m =
    case minState m of
        Just (x, m') -> runReducer' red hal ord config pr x m'
        Nothing -> return []

updateExStateHalter :: Halter h hv t => h -> Processed (ExState hv sov t) -> ExState hv sov t -> ExState hv sov t
updateExStateHalter hal proc es@ExState {state = s, halter_val = hv} =
    let
        hv' = updatePerStateHalt hal hv (processedToState proc) s
    in
    es {halter_val = hv'}

processedToState :: Processed (ExState hv sov t) -> Processed (State t)
processedToState (Processed {accepted = app, discarded = dis}) =
    Processed {accepted = map state app, discarded = map state dis}

-- Uses the Orderer to determine which state to continue execution on.
-- Returns that State, and a list of the rest of the states 
minState :: Ord b => M.Map b [ExState hv sov t] -> Maybe ((ExState hv sov t), M.Map b [ExState hv sov t])
minState m =
    case M.minViewWithKey m of
      Just ((k, x:xs), _) -> Just (x, M.insert k xs m)
      Just ((_, []), m') -> minState m'
      Nothing -> Nothing

numStates :: M.Map b [ExState hv sov t] -> Int
numStates = sum . map length . M.elems

outputState :: String -> [Int] -> State t -> IO ()
outputState fdn is s = do
    let dir = fdn ++ "/" ++ foldl' (\str i -> str ++ show i ++ "/") "" is
    createDirectoryIfMissing True dir

    let fn = dir ++ "state" ++ show (length $ rules s) ++ ".txt"
    let write = pprExecStateStr s
    writeFile fn write

    putStrLn fn
