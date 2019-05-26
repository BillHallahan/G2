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
                            , mapProcessed

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
                            , Logger (..)

                            , (<~)
                            , (<~?)
                            , (<~|)

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

                            , runReducer 
                            , runReducerMerge ) where

import qualified G2.Language.ExprEnv as E
import G2.Execution.Rules
import G2.Language
import qualified G2.Language.Stack as Stck
import G2.Solver
import G2.Lib.Printers
import G2.Execution.StateMerging

import Data.Foldable
import qualified Data.HashSet as S
import qualified Data.Map as M
import Data.Maybe
import qualified Data.List as L
import System.Directory

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
data ReducerRes = NoProgress | InProgress | Finished | Merge | MergePoint deriving (Eq, Ord, Show, Read)

progPrioritizer :: ReducerRes -> ReducerRes -> ReducerRes
progPrioritizer Merge _ = Merge
progPrioritizer _ Merge = Merge
progPrioritizer MergePoint _ = MergePoint
progPrioritizer _ MergePoint = MergePoint
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
    -- | Gives an opportunity to update with all States and Reducer Val's,
    -- output by all Reducer's, visible
    -- Errors if the returned list is too short.
    {-# INLINE updateWithAll #-}
    updateWithAll :: r -> [(State t, rv)] -> [rv]
    updateWithAll _ = map snd 


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
    stopRed :: h -> hv -> Processed (State t) -> State t -> HaltC

    -- | Takes a state, and updates it's halter record field
    stepHalter :: h -> hv -> Processed (State t) -> State t -> hv

-- | Picks an order to evaluate the states, to allow prioritizing some over others 
-- The type parameter or is used to disambiguate between different producers.
-- To create a new reducer, define some new type, and use it as or.
class Ord b => Orderer or sov b t | or -> sov, or -> b where
    -- | Initializing the per state ordering value 
    initPerStateOrder :: or -> State t -> sov

    -- | Assigns each state some value of an ordered type, and then proceeds with execution on the
    -- state assigned the minimal value
    orderStates :: or -> sov -> State t -> b

    -- | Run on the selected state, to update it's sov field
    updateSelected :: or -> sov -> Processed (State t) -> State t -> sov

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
                     deriving (Eq, Show, Read)

-- We use RC to combine the reducer values for RCombiner
-- We should never define any other instance of Reducer with RC, or export it
-- because this could lead to undecidable instances
data RC a b = RC a b

instance (Reducer r1 rv1 t, Reducer r2 rv2 t) => Reducer (RCombiner r1 r2) (RC rv1 rv2) t where
    initReducer (r1 :<~ r2) s =
        let
            rv1 = initReducer r1 s
            rv2 = initReducer r2 s
        in
        RC rv1 rv2
    initReducer (r1 :<~? r2) s =
        let
            rv1 = initReducer r1 s
            rv2 = initReducer r2 s
        in
        RC rv1 rv2
    initReducer (r1 :<~| r2) s =
        let
            rv1 = initReducer r1 s
            rv2 = initReducer r2 s
        in
        RC rv1 rv2

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

    updateWithAll (r1 :<~ r2) = updateWithAllRC r1 r2
    updateWithAll (r1 :<~? r2) = updateWithAllRC r1 r2
    updateWithAll (r1 :<~| r2) = updateWithAllRC r1 r2

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

-- Applies function to first (State t, rv2), gets new Bindings and recursively applies function to rest of array using new Bindings
mapMAccumB :: (Bindings -> (State t, rv2) -> IO (Bindings, (ReducerRes, [(State t, RC rv rv2)], r))) -> Bindings -> [(State t, rv2)] 
        -> IO (Bindings, [(ReducerRes, [(State t, RC rv rv2)], r)])
mapMAccumB _ b [] = do
    return (b, [])
mapMAccumB f b (x:xs) = do
    (b', res) <- f b x
    (b'', res2) <- mapMAccumB f b' xs
    return $ (b'', res:res2)

redRulesToStatesAux :: Reducer r rv t => r -> rv -> Bindings -> (State t, rv2) -> IO (Bindings, (ReducerRes, [(State t, RC rv rv2)], r))
redRulesToStatesAux r rv1 b (is, rv2) = do
        (rr_, is', b', r') <- redRules r rv1 is b
        return (b', (rr_, map (\(is'', rv1') -> (is'', RC rv1' rv2) ) is', r'))
    
redRulesToStates :: Reducer r rv t => r -> rv -> [(State t, rv2)] -> Bindings -> IO (ReducerRes, [(State t, RC rv rv2)], Bindings, r)
redRulesToStates r rv1 s b = do
    let redRulesToStatesAux' = redRulesToStatesAux r rv1
    (b', rs) <- mapMAccumB redRulesToStatesAux' b s

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

data StdRed con = StdRed con

instance Solver con => Reducer (StdRed con) () t where
    initReducer _ _ = ()

    redRules stdr@(StdRed solver) _ s b = do
        (r, s', b') <- stdReduce solver s b
        let res = case r of
                    RuleHitMergePt -> MergePoint
                    RuleEvalCaseSym -> Merge
                    RuleIdentity -> Finished
                    _ -> InProgress
        
        return (res, s', b', stdr)

-- | Removes and reduces the values in a State's non_red_path_conds field. 
data NonRedPCRed = NonRedPCRed

instance Reducer NonRedPCRed () t where
    initReducer _ _ = ()

    redRules nrpr _  s@(State { expr_env = eenv
                              , curr_expr = cexpr
                              , exec_stack = stck
                              , non_red_path_conds = nr:nrs
                              , symbolic_ids = si
                              , model = m })
                      b@(Bindings { higher_order_inst = inst }) = do
        let stck' = Stck.push (CurrExprFrame cexpr) stck

        let cexpr' = CurrExpr Evaluate nr

        let eenv_si_ces = substHigherOrder eenv m si inst cexpr'

        let s' = s { exec_stack = stck'
                   , non_red_path_conds = nrs
                   }
            xs = map (\(eenv', m', si', ce) -> (s' { expr_env = eenv'
                                                   , model = m'
                                                   , curr_expr = ce
                                                   , symbolic_ids = si' }, ())) eenv_si_ces

        return (InProgress, xs, b, nrpr)
    redRules nrpr _ s b = return (Finished, [(s, ())], b, nrpr)

-- [Higher-Order Model]
-- Substitutes all possible higher order functions for symbolic higher order functions.
-- We insert the substituted higher order function directly into the model, because, due
-- to the VAR-RED rule, the function name will (if the function is called) be lost during execution.
substHigherOrder :: ExprEnv -> Model -> SymbolicIds -> [Name] -> CurrExpr -> [(ExprEnv, Model, SymbolicIds, CurrExpr)]
substHigherOrder eenv m si ns ce =
    let
        is = mapMaybe (\n -> case E.lookup n eenv of
                                Just e -> Just $ Id n (typeOf e)
                                Nothing -> Nothing) ns

        higherOrd = filter (isTyFun . typeOf) . mapMaybe varId . symbVars eenv $ ce
        higherOrdSub = map (\v -> (v, mapMaybe (genSubstitutable v) is)) higherOrd
    in
    substHigherOrder' [(eenv, m, si, ce)] higherOrdSub
    where
        genSubstitutable v i
            | (True, bm) <- specializes M.empty (typeOf v )(typeOf i) =
                let
                    bnds = map idName $ leadingTyForAllBindings i
                    tys = mapMaybe (\b -> fmap Type $ M.lookup b bm) bnds
                in
                Just . mkApp $ Var i:tys
            | otherwise = Nothing

substHigherOrder' :: [(ExprEnv, Model, SymbolicIds, CurrExpr)] -> [(Id, [Expr])] -> [(ExprEnv, Model, SymbolicIds, CurrExpr)]
substHigherOrder' eenvsice [] = eenvsice
substHigherOrder' eenvsice ((i, es):iss) =
    substHigherOrder'
        (concatMap (\e_rep -> 
                        map (\(eenv, m, si, ce) -> ( E.insert (idName i) e_rep eenv
                                                   , M.insert (idName i) e_rep m
                                                   , filter (/= i) si
                                                   , replaceASTs (Var i) e_rep ce)
                            ) eenvsice)
        es) iss

data TaggerRed = TaggerRed Name NameGen

instance Reducer TaggerRed () t where
    initReducer _ _ = ()

    redRules tr@(TaggerRed n ng) _ s@(State {tags = ts}) b =
        let
            (n'@(Name n_ m_ _ _), ng') = freshSeededName n ng
        in
        if null $ S.filter (\(Name n__ m__ _ _) -> n_ == n__ && m_ == m__) ts then
            return (Finished, [(s {tags = S.insert n' ts}, ())], b, TaggerRed n ng')
        else
            return (Finished, [(s, ())], b, tr)

-- | A Reducer to producer logging output 
data Logger = Logger String

instance Reducer Logger [Int] t where
    initReducer _ _ = []

    redRules l@(Logger fn) li s b = do
        outputState fn li s b
        return (NoProgress, [(s, li)], b, l)
    
    updateWithAll _ [(_, l)] = [l]
    updateWithAll _ ss = map (\(l, i) -> l ++ [i]) $ zip (map snd ss) [1..]

outputState :: String -> [Int] -> State t -> Bindings -> IO ()
outputState fdn is s b = do
    let dir = fdn ++ "/" ++ foldl' (\str i -> str ++ show i ++ "/") "" is
    createDirectoryIfMissing True dir

    let fn = dir ++ "state" ++ show (length $ rules s) ++ ".txt"
    let write = pprExecStateStr s b
    writeFile fn write

    putStrLn fn


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
    initHalt _ _ = ()
    updatePerStateHalt _ _ _ _ = ()
    stopRed _ _ _ s =
        case isExecValueForm s && true_assert s of
            True -> Accept
            False -> Continue
    stepHalter _ _ _ _ = ()

-- | Allows execution to continue until the step counter hits 0, then discards the state
data ZeroHalter = ZeroHalter Int

instance Halter ZeroHalter Int t where
    initHalt (ZeroHalter n) _ = n
    updatePerStateHalt _ hv _ _ = hv
    stopRed = halterIsZero
    stepHalter = halterSub1

halterSub1 :: Halter h Int t => h -> Int -> Processed (State t) -> State t -> Int
halterSub1 _ h _ _ = h - 1

halterIsZero :: Halter h Int t => h -> Int -> Processed (State t) -> State t -> HaltC
halterIsZero _ 0 _ _ = Discard
halterIsZero _ _ _ _ = Continue

data MaxOutputsHalter = MaxOutputsHalter (Maybe Int)

instance Halter MaxOutputsHalter (Maybe Int) t where
    initHalt (MaxOutputsHalter m) _ = m
    updatePerStateHalt _ hv _ _ = hv
    stopRed _ m (Processed {accepted = acc}) _ =
        case m of
            Just m' -> if length acc >= m' then Discard else Continue
            _ -> Continue
    stepHalter _ hv _ _ = hv

-- | Switch execution every n steps
data SwitchEveryNHalter = SwitchEveryNHalter Int

instance Halter SwitchEveryNHalter Int t where
    initHalt (SwitchEveryNHalter sw) _ = sw
    updatePerStateHalt (SwitchEveryNHalter sw) _ _ _ = sw
    stopRed _ i _ _ = if i <= 0 then Switch else Continue
    stepHalter _ i _ _ = i - 1

-- | If the Name, disregarding the Unique, in the DiscardIfAcceptedTag
-- matches a Tag in the Accepted State list,
-- and in the State being evaluated, discard the State
data DiscardIfAcceptedTag = DiscardIfAcceptedTag Name 

instance Halter DiscardIfAcceptedTag (S.HashSet Name) t where
    initHalt _ _ = S.empty
    
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
    initPerStateOrder _ _ = ()
    orderStates _ _ _ = 0
    updateSelected _ v _ _ = v

-- | Continue execution on the state that has been picked the least in the past. 
data PickLeastUsedOrderer = PickLeastUsedOrderer

instance Orderer PickLeastUsedOrderer Int Int t where
    initPerStateOrder _ _ = 0
    orderStates _ v _ = v
    updateSelected _ v _ _ = v + 1

--------
--------

-- | Uses a passed Reducer, Halter and Orderer to execute the reduce on the State, and generated States
runReducer :: (Reducer r rv t, Halter h hv t, Orderer or sov b t) => r -> h -> or -> State t -> Bindings -> IO ([State t], Bindings)
runReducer red hal ord s b = do
    let pr = Processed {accepted = [], discarded = []}
    let s' = ExState { state = s
                    , reducer_val = initReducer red s
                    , halter_val = initHalt hal s
                    , order_val = initPerStateOrder ord s }

    (states, b') <- runReducer' red hal ord pr s' b M.empty
    states' <- mapM (\ExState {state = st} -> return st) states
    return (states', b')

runReducer' :: (Reducer r rv t, Halter h hv t, Orderer or sov b t) 
            => r 
            -> h 
            -> or 
            -> Processed (ExState rv hv sov t) 
            -> ExState rv hv sov t 
            -> Bindings
            -> M.Map b [ExState rv hv sov t] 
            -> IO ([ExState rv hv sov t], Bindings)
runReducer' red hal ord  pr rs@(ExState { state = s, reducer_val = r_val, halter_val = h_val }) b xs
    | hc == Accept =
        let
            pr' = pr {accepted = rs:accepted pr}
            jrs = minState xs
        in
        case jrs of
            Just (rs', xs') -> do
                (states, b') <- runReducer' red hal ord pr' (updateExStateHalter hal pr' rs') b xs'
                return (rs:states, b')
            Nothing -> return ([rs], b)
    | hc == Discard =
        let
            pr' = pr {discarded = rs:discarded pr}
            jrs = minState xs
        in
        case jrs of
            Just (rs', xs') -> runReducer' red hal ord pr' (updateExStateHalter hal pr' rs') b xs'
            Nothing -> return ([], b)
    | hc == Switch =
        let
            k = orderStates ord (order_val rs') (state rs)
            rs' = rs { order_val = updateSelected ord (order_val rs) ps (state rs) }

            Just (rs'', xs') = minState (M.insertWith (++) k [rs'] xs)
            
            rs''' = rs'' { halter_val = updatePerStateHalt hal (halter_val rs'') ps (state rs'') }
        in
        if not $ discardOnStart hal (halter_val rs''') ps (state rs''')
            then runReducer' red hal ord pr rs''' b xs'
            else runReducerList red hal ord (pr {discarded = rs''':discarded pr}) xs' b
    | otherwise = do
        (_, reduceds, b', red') <- redRules red r_val s b
        let reduceds' = map (\(r, rv) -> (r {num_steps = num_steps r + 1}, rv)) reduceds

        let r_vals = updateWithAll red reduceds' ++ error "List returned by updateWithAll is too short."
        
        let mod_info = map (\(s', r_val') -> rs { state = s'
                                                , reducer_val = r_val'
                                                , halter_val = stepHalter hal h_val ps s'}) $ zip (map fst reduceds') r_vals
        
        let xs' = foldr (\s' -> M.insertWith (++) (orderStates ord (order_val s') (state s')) [s']) xs mod_info

        runReducerList red' hal ord pr xs' b'
    where
        hc = stopRed hal h_val ps s
        ps = processedToState pr

runReducerList :: (Reducer r rv t, Halter h hv t, Orderer or sov b t) 
               => r 
               -> h 
               -> or 
               -> Processed (ExState rv hv sov t)
               -> M.Map b [ExState rv hv sov t]
               -> Bindings
               -> IO ([ExState rv hv sov t], Bindings)
runReducerList red hal ord pr m binds =
    case minState m of
        Just (x, m') -> runReducer' red hal ord pr x binds m'
        Nothing -> return ([], binds)

updateExStateHalter :: Halter h hv t
                    => h
                    -> Processed (ExState rv hv sov t)
                    -> ExState rv hv sov t
                    -> ExState rv hv sov t
updateExStateHalter hal proc es@ExState {state = s, halter_val = hv} =
    let
        hv' = updatePerStateHalt hal hv (processedToState proc) s
    in
    es {halter_val = hv'}

processedToState :: Processed (ExState rv hv sov t) -> Processed (State t)
processedToState (Processed {accepted = app, discarded = dis}) =
    Processed {accepted = map state app, discarded = map state dis}

-- Uses the Orderer to determine which state to continue execution on.
-- Returns that State, and a list of the rest of the states 
minState :: Ord b => M.Map b [ExState rv hv sov t] -> Maybe ((ExState rv hv sov t), M.Map b [ExState rv hv sov t])
minState m =
    case M.minViewWithKey m of
      Just ((k, x:xs), _) -> Just (x, M.insert k xs m)
      Just ((_, []), m') -> minState m'
      Nothing -> Nothing

numStates :: M.Map b [ExState rv hv sov t] -> Int
numStates = sum . map length . M.elems

------
type Counter = Int
type MergeState = Bool
data Tree a = Tree a [Tree a] Counter MergeState

treeVal :: Tree a -> a
treeVal (Tree a _ _ _) = a

runReducerMerge :: (Eq t, Reducer r rv t, Halter h hv t) => r -> h -> State t -> Bindings -> IO([State t], Bindings)
runReducerMerge red hal s b = do
    let pr = Processed {accepted = [], discarded = []}
    let s' = ExState {state = s, halter_val = initHalt hal s, reducer_val = initReducer red s, order_val = Nothing}
    let evalTree = Tree [s'] [] 0 False
    (exStates, b') <- runReducerMerge' red hal pr evalTree b

    states <- mapM (\ExState {state = st} -> return st) exStates
    return (states, b')

runReducerMerge' :: (Eq t, Reducer r rv t, Halter h hv t) => r -> h -> Processed (ExState rv hv sov t) -> Tree [ExState rv hv sov t] -> Bindings -> IO ([ExState rv hv sov t], Bindings)
runReducerMerge' red hal pr evalTree b = do
    (maybeNewEvalTree, b', red', hal', pr') <- evalLeaf red hal pr evalTree b
    case maybeNewEvalTree of
        (Just newEvalTree) -> runReducerMerge' red' hal' pr' newEvalTree b'
        Nothing -> return (accepted pr', b')

evalLeaf :: (Eq t, Reducer r rv t, Halter h hv t) => r -> h -> Processed (ExState rv hv sov t) -> Tree [ExState rv hv sov t] -> Bindings -> IO (Maybe (Tree [ExState rv hv sov t]), Bindings, r, h, Processed (ExState rv hv sov t))
evalLeaf red hal pr (Tree a children count mergeSt) b
    | [] <- children -- leaf node, execute state contained in node
    , [x] <- a = do -- should only have one state in 'a', other cases should have split tree earlier
        -- print "Case 1"
        let rs@(ExState {state = s, halter_val = h_val, reducer_val = r_val}) = x 
        let ps = processedToState pr
        let hc = stopRed hal h_val ps s
        case hc of
            Accept -> do
                -- print (length (rules s))
                -- print "Accepted"
                let pr' = pr {accepted = rs:accepted pr} -- we do not call updateExStateHalter for now, since we do not deal with any Switch constructors
                return (Nothing, b, red, hal, pr')
            Discard -> do
                let pr' = pr {discarded = rs:discarded pr}
                return (Nothing, b, red, hal, pr')
            _ -> do -- ignore switch for now
                (reducerRes, reduceds, b', red') <- redRules red r_val s b
                case reduceds of
                    [] -> return (Nothing, b', red', hal, pr)
                    _ -> do
                        let reduceds' = map (\(r, rv) -> (r {num_steps = num_steps r + 1}, rv)) reduceds
                        let r_vals = updateWithAll red reduceds' ++ error "List returned by updateWithAll is too short.."
                        let reduceds'' = map (\(s', r_val') -> rs { state = s'
                                                                    , reducer_val = r_val'
                                                                    , halter_val = stepHalter hal h_val ps s'})
                                                                    $ zip (map fst reduceds') r_vals
                        case reducerRes of
                            MergePoint -> return (Just (Tree reduceds'' [] (count - 1) False), b', red', hal, pr)
                            Merge -> do
                                let newChildren = map (\r -> Tree [r] [] (count+1) False) reduceds''
                                let newTree = Tree a newChildren count True
                                return (Just newTree, b', red', hal, pr)
                            _ -> do
                                let newChildren = map (\r -> Tree [r] [] count False) reduceds''
                                -- print (length newChildren)
                                let newTree = Tree a newChildren count False
                                return (Just newTree, b', red', hal, pr)
    | (_:_) <- children -- not a leaf node
    , mergeSt -- children are a result of splitting on a symbolic value
    , not $ mergePtCountsOk children count -- not all children in  SWHNF (i.e. not ready to merge)
    , (Just child, rest) <- pickMaxChild (splitNodes children) = do
        -- print "Case 2"
        (maybNewChild, b', red', hal', pr') <- evalLeaf red hal pr child b
        let children' = case maybNewChild of
                        (Just c) ->  c:rest
                        Nothing -> rest
        -- print "Case 2 end"
        case children' of
            [] -> return $ (Nothing, b', red', hal', pr')
            _ -> return $ (Just (Tree a children' count mergeSt), b', red', hal', pr')
    | (_:_) <- children
    , mergeSt -- children are a result of splitting on a symbolic value
    , mergePtCountsOk children count = do -- states in all children are in SWHNF, ready to merge
        -- print "Case 3"
        -- putStrLn "Children length: "
        -- putStrLn $ show (length (concat (map treeVal children)))
        let (mergedStates, b') = mergeStates (map treeVal children) b
        -- putStrLn "Merged States length: "
        -- putStrLn $ show (length mergedStates)
        let count' = (\(Tree _ _ cnt _) -> cnt) (head children)
        if count' == 0
            then -- top level merge point, so no need to clump states together if they can't be merged
                let children' = map (\exS -> Tree [exS] [] count' False) mergedStates
                in return (Just (Tree a children' count' False), b', red, hal, pr)
            else
                return (Just (Tree mergedStates [] count' False), b', red, hal, pr)
    | (_:_) <- children
    , not mergeSt
    , ((\(Tree _ _ c _) -> c) (head children)) < count -- children are result of having merged states, need to propagate them up the tree
    , mergePtCountsOk children count = do
        -- print "Case 4"
        let children' = concat $ map (treeVal) children
        let count' = (\(Tree _ _ cnt _) -> cnt) (head children)
        return (Just (Tree children' [] count' False), b, red, hal, pr)
    | (_:_) <- children -- Picks any child to evaluate
    , (Just child, rest) <- pickMaxChild (splitNodes children) = do
        -- print "Case 5"
        -- let (child, rest) = pickMaxChild (splitNodes children)
        (maybNewChild, b', red', hal', pr') <- evalLeaf red hal pr child b
        let children' = case maybNewChild of
                        (Just c) ->  c:rest
                        Nothing -> rest
        -- print "children length: "
        -- print (length children')
        -- print "Case 5 end"
        case children' of
            [] -> return $ (Nothing, b', red', hal', pr')
            [x] -> return $ (Just x, b', red', hal', pr') -- optimization to reduce depth of tree
            _ -> return $ (Just (Tree a children' count mergeSt), b', red', hal', pr')
     | otherwise = error "Unable to evaluate tree."

splitNodes :: [Tree [ExState rv hv sov t]] -> [Tree [ExState rv hv sov t]]
splitNodes ((Tree a subTrees count mergeSt):xs) = case a of
    (_:_) -> (map (\exS -> (Tree [exS] subTrees count mergeSt)) a) ++ (splitNodes xs) -- subTrees should be [] when called earlier
    [] -> (Tree a subTrees count mergeSt) : (splitNodes xs) -- ensure at least one leaf is returned
splitNodes [] = []

mergePtCountsOk :: [Tree [ExState rv hv sov t]] -> Int -> Bool
mergePtCountsOk [] _ = True
mergePtCountsOk leaves@(_:_) count = (all (== (head counts)) counts) && (all (<= count) counts)
    where
        counts = (map getCount leaves)
        getCount = (\(Tree _ _ c _) -> c)

pickMaxChild :: [Tree [ExState rv hv sov t]] -> (Maybe (Tree [ExState rv hv sov t]), [Tree [ExState rv hv sov t]])
pickMaxChild [] = (Nothing, [])
pickMaxChild leaves@(_:_) = pickMaxChild' [] (head leaves) (tail leaves) -- return tree with maximum count, and rest

pickMaxChild' :: [Tree [ExState rv hv sov t]] -> Tree [ExState rv hv sov t] -> [Tree [ExState rv hv sov t]] -> (Maybe (Tree [ExState rv hv sov t]), [Tree [ExState rv hv sov t]])
pickMaxChild' seen maxT [] = (Just maxT, seen)
pickMaxChild' seen maxT (x:xs) = if xCount > maxCount
    then pickMaxChild' (maxT:seen) x xs --reverses order of leafs, maybe avoid?
    else pickMaxChild' (x:seen) maxT xs
    where
        xCount = (\(Tree _ _ c _) -> c) x
        maxCount = (\(Tree _ _ c _) -> c) maxT

pickAnyChild :: [Tree [ExState rv hv sov t]] -> (Tree [ExState rv hv sov t], [Tree [ExState rv hv sov t]])
pickAnyChild [] = error "Should only be called with at least 1 Tree in list"
pickAnyChild (x:xs) = (x, xs)

mergeStates :: Eq t => [[ExState rv hv sov t]] -> Bindings -> ([ExState rv hv sov t], Bindings)
mergeStates ls@(x1:x2:xs) b
    | all (==1) (map length ls) = case mergeStates' (head x1) (head x2) b of
        (Just exS, b') -> mergeStates (([exS]):xs) b'
        (Nothing, b') -> (concat ls, b')
    | otherwise = (concat ls, b)
mergeStates ls b = (concat ls, b)

mergeStates' :: Eq t => (ExState rv hv sov t) -> (ExState rv hv sov t) -> Bindings -> (Maybe (ExState rv hv sov t), Bindings)
mergeStates' ex1 ex2 b = 
    let s1 = state ex1
        s2 = state ex2
        ng = name_gen b
        res = mergeState ng s1 s2
    in case res of
        (ng', Just s') -> (Just ex1 {state = s'}, b {name_gen = ng'}) -- todo: which reducer_val and halter_val to keep
        (ng', Nothing) -> (Nothing, b {name_gen = ng'})

------------
-- recursion based runReducer that does state merging 

-- runReducerMerge :: (Reducer r rv t, Halter h hv t) => r -> h -> Processed (ExState rv hv sov t) -> [ExState rv hv sov t] -> Bindings -> IO ([ExState rv hv sov t],Bindings,r)
-- runReducerMerge red hal pr mergeableStates b = do
--    (mpStates, b', red') <- runReducerMerge' red hal pr mergeableStates b
--    return $ (\(ms,binds) -> (ms, binds, red')) $ mergeStates mpStates b'

--runReducerMerge' :: (Reducer r rv t, Halter h hv t) => r -> h -> Processed (ExState rv hv sov t) -> [ExState rv hv sov t] -> Bindings -> IO ([[ExState rv hv sov t]],Bindings,r)
--runReducerMerge' red hal pr mergeableStates b
--    | (x:xs) <- mergeableStates = do
--        (mpStates, b', red') <- evalStateTillMP red hal pr x b
--        (mpStates', b'', red'') <- runReducerMerge' red' hal pr xs b'
--        return $ (mpStates:mpStates', b'', red'')
--    | [] <- mergeableStates = return ([], b, red)

--evalStateTillMP :: (Reducer r rv t, Halter h hv t) => r -> h -> Processed (ExState rv hv sov t) -> ExState rv hv sov t -> Bindings -> IO ([ExState rv hv sov t],Bindings,r)
--evalStateTillMP red hal pr rs@(ExState {state = s, reducer_val = r_val, halter_val = h_val}) b = do
--    (reducerRes, reduceds, b', red') <- redRules red r_val s b
--    case reducerRes of
--        MergePoint -> return ([rs], b, red)
--        _ -> do
--            let mergeableStates = map (\(r, rv) -> (r {num_steps = num_steps r + 1}, rv)) reduceds
--            let r_vals = updateWithAll red mergeableStates ++ error "List returned by updateWithAll is too short.."
--            let ps = processedToState pr
--            let mergeableStates' = map (\(s', r_val') -> rs { state = s'
--                                                             , reducer_val = r_val'
--                                                             , halter_val = stepHalter hal h_val ps s'})
--                                                             $ zip (map fst mergeableStates) r_vals
--            (mergedStates, b'', red'') <- runReducerMerge red' hal pr mergeableStates' b'
--            return (mergedStates, b'', red'')

-- runReducerList :: (Reducer r rv t, Halter h hv t) => r -> h -> Processed (ExState rv hv sov t) -> [ExState rv hv sov t] -> Bindings -> IO ([ExState rv hv sov t], Bindings)
-- runReducerList red hal pr xs b = case xs of
--    (x:xs') -> runReducer' red hal pr x b xs'
--    [] -> return ([], b)
