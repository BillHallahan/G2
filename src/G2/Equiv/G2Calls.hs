{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Equiv.G2Calls ( StateET
                        , emptyEquivTracker
                        , runG2ForRewriteV) where

import G2.Config
import G2.Execution
import G2.Interface
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Solver

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Text ()

import Debug.Trace

import qualified Data.Text as T

import qualified G2.Language.Stack as Stck

-- TODO
import Data.Maybe
import G2.Execution.Reducer ( EquivTracker )

-- get names from symbolic ids in the state
runG2ForRewriteV :: StateET ->
                    Config ->
                    Bindings ->
                    HS.HashSet Name ->
                    IO ([ExecRes EquivTracker], Bindings)
runG2ForRewriteV state config bindings total = do
    SomeSolver solver <- initSolver config
    let simplifier = IdSimplifier
        sym_config = PreserveAllMC
        -- sym_config = addSearchNames (names $ track state)
        --            $ addSearchNames (input_names bindings) emptyMemConfig

        state' = state { track = (track state) { saw_tick = Nothing } }

    (in_out, bindings') <- case rewriteRedHaltOrd solver simplifier config total of
                (red, hal, ord) ->
                    runG2WithSomes red hal ord solver simplifier sym_config state' bindings

    close solver

    return (in_out, bindings')

rewriteRedHaltOrd :: (Solver solver, Simplifier simplifier) =>
                     solver ->
                     simplifier ->
                     Config ->
                     HS.HashSet Name ->
                     (SomeReducer EquivTracker, SomeHalter EquivTracker, SomeOrderer EquivTracker)
rewriteRedHaltOrd solver simplifier config total =
    let
        share = sharing config
        state_name = Name "state" Nothing 0 Nothing
    in
    (case logStates config of
            Just fp -> SomeReducer (StdRed share solver simplifier :<~ EnforceProgressR :<~ ConcSymReducer :<~? (Logger fp :<~ EquivReducer))
            Nothing -> SomeReducer (StdRed share solver simplifier :<~ EnforceProgressR :<~ ConcSymReducer :<~? EquivReducer)
     , SomeHalter
         (DiscardIfAcceptedTag state_name
         :<~> EnforceProgressH
         :<~> SWHNFHalter)
     , SomeOrderer $ PickLeastUsedOrderer)

type StateET = State EquivTracker

data EnforceProgressR = EnforceProgressR

data EnforceProgressH = EnforceProgressH

instance Reducer EnforceProgressR () EquivTracker where
    initReducer _ _ = ()
    redRules r rv s@(State { curr_expr = CurrExpr _ e
                           , num_steps = n
                           , track = EquivTracker et m total })
                  b =
        let s' = s { track = EquivTracker et (Just n) total }
        in
        case (e, m) of
            (Tick (NamedLoc (Name p _ _ _)) _, Nothing) ->
                if p == T.pack "STACK"
                then return (InProgress, [(s', ())], b, r)
                else return (NoProgress, [(s, ())], b, r)
            -- TODO condense these into one case?
            -- then again, it might not matter at all here
            (Tick (NamedLoc (Name p _ _ _)) _, Just n0) ->
                if p == T.pack "STACK" && n > n0 + 1
                then return (InProgress, [(s', ())], b, r)
                else return (NoProgress, [(s, ())], b, r)
            _ -> return (NoProgress, [(s, rv)], b, r)

argCount :: Type -> Int
argCount = length . spArgumentTypes . PresType

exprFullApp :: ExprEnv -> Expr -> Bool
exprFullApp h e | (Tick (NamedLoc (Name p _ _ _)) f):args <- unApp e
                , p == T.pack "REC" = exprFullApp h (mkApp $ f:args)
exprFullApp h e | (Var (Id n t)):_ <- unApp e
                -- We require that the variable be the center of a function
                -- application, have at least one argument, and not map to a variable for two reasons:
                -- (1) We do not want to count symbolic function applications as in FAF form
                -- (2) We need to ensure we make sufficient progress to avoid
                -- moreRestrictive matching states spuriously.
                -- Consider an expression environment with a mapping of `x :: Int` to `f y`.
                -- We want to avoid storing a previous state using x,
                -- having the symbolic execution inline `f y`, and then deciding that 
                -- the two states match and are sufficient for verification to succeed,
                -- when, in isMoreRestrictive, x is inlined.
                , Just e' <- E.lookup n h
                , not (isVar e')
                , c_unapp <- length (unApp e)
                , c_unapp >= 2 = c_unapp == 1 + argCount t
exprFullApp _ _ = False

isVar :: Expr -> Bool
isVar (Var _) = True
isVar _ = False

containsCase :: Stck.Stack Frame -> Bool
containsCase sk =
    case Stck.pop sk of
        Nothing -> False
        Just (CaseFrame _ _, _) -> True
        Just (_, sk') -> containsCase sk'

-- induction only works if both states in a pair satisfy this
-- there's no harm in stopping here for just one, though
recursionInCase :: State t -> Bool
recursionInCase (State { curr_expr = CurrExpr _ e, exec_stack = sk }) =
    case e of
        Tick (NamedLoc (Name p _ _ _)) _ ->
            p == T.pack "REC" && containsCase sk
        _ -> False

instance Halter EnforceProgressH () EquivTracker where
    initHalt _ _ = ()
    updatePerStateHalt _ _ _ _ = ()
    stopRed _ _ _ s =
        let CurrExpr _ e = curr_expr s
            n' = num_steps s
            EquivTracker _ m _ = track s
            h = expr_env s
        in
        case m of
            Nothing -> return Continue
            -- Execution needs to take strictly more than one step beyond the
            -- point when it reaches the Tick because the act of unwrapping the
            -- expression inside the Tick counts as one step.
            Just n0 -> do
                if (isExecValueForm s) || (exprFullApp h e) || (recursionInCase s)
                       then return (if n' > n0 + 1 then Accept else Continue)
                       else return Continue
    stepHalter _ _ _ _ _ = ()

-- Maps higher order function calles to symbolic replacements.
-- This allows the same call to be replaced by the same Id consistently.
{-
data EquivTracker = EquivTracker { higher_order :: HM.HashMap Expr Id
                                 , saw_tick :: Maybe Int
                                 , total :: HS.HashSet Name } deriving Show
-}

emptyEquivTracker :: EquivTracker
emptyEquivTracker = EquivTracker HM.empty Nothing HS.empty

data EquivReducer = EquivReducer

instance Reducer EquivReducer () EquivTracker where
    initReducer _ _ = ()
    redRules r _
                 s@(State { expr_env = eenv
                          , curr_expr = CurrExpr Evaluate e
                          , symbolic_ids = symbs
                          , track = EquivTracker et m total })
                 b@(Bindings { name_gen = ng })
        | isSymFuncApp eenv e =
            let
                -- We inline variables to have a higher chance of hitting in the Equiv Tracker
                e' = inlineApp eenv e
            in
            case HM.lookup e' et of
                Just v ->
                    let
                        s' = s { curr_expr = CurrExpr Evaluate (Var v) }
                    in
                    return (InProgress, [(s', ())], b, r)
                Nothing ->
                    let
                        (v, ng') = freshId (typeOf e) ng
                        et' = trace ("FRESH " ++ show v) $ HM.insert e' v et
                        -- TODO carry over totality if function and arg are total
                        -- unApp, make sure every arg is a symbolic var
                        -- they also need to be total
                        -- this case means this combination has not been tried before
                        -- TODO are they all inlined by now?
                        -- TODO get all the var names from inside first
                        -- these are exprs originally
                        -- TODO new total not being carried over to ConcSymReducer
                        es = trace ("ALL " ++ show total) $ map exprVarName $ unApp e'
                        all_vars = trace ("EXPRS " ++ show es) $ foldr (&&) True $ map isJust es
                        es' = map (\(Just n) -> n) $ filter isJust es
                        all_sym = foldr (&&) True $ map (\x -> E.isSymbolic x eenv) es'
                        all_total = foldr (&&) True $ map (`elem` total) es'
                        total' = if all_vars && all_sym && all_total
                                 then trace ("SUCCESS " ++ show v) HS.insert (idName v) total
                                 else total
                        s' = s { curr_expr = CurrExpr Evaluate (Var v)
                               , track = EquivTracker et' m total'
                               , expr_env = E.insertSymbolic (idName v) v eenv
                               , symbolic_ids = v:symbs }
                        b' = b { name_gen = ng' }
                    in
                    return (InProgress, [(s', ())], b', r)
    redRules r rv s b = return (NoProgress, [(s, rv)], b, r)

exprVarName :: Expr -> Maybe Name
exprVarName (Var i) = Just $ idName i
exprVarName _ = Nothing

isSymFuncApp :: ExprEnv -> Expr -> Bool
isSymFuncApp eenv e
    | v@(Var _):(_:_) <- unApp e
    , (Var (Id f t)) <- inlineVars eenv v =
       E.isSymbolic f eenv && hasFuncType (PresType t)
    | otherwise = False

inlineApp :: ExprEnv -> Expr -> Expr
inlineApp eenv = mkApp . map (inlineVars eenv) . unApp

inlineVars :: ExprEnv -> Expr -> Expr
inlineVars = inlineVars' HS.empty

inlineVars' :: HS.HashSet Name -> ExprEnv -> Expr -> Expr
inlineVars' seen eenv (Var (Id n _))
    | not (n `HS.member` seen)
    , Just e <- E.lookup n eenv = inlineVars' (HS.insert n seen) eenv e
inlineVars' seen eenv (App e1 e2) = App (inlineVars' seen eenv e1) (inlineVars' seen eenv e2)
inlineVars' _ _ e = e

instance ASTContainer EquivTracker Expr where
    containedASTs (EquivTracker hm _ _) = HM.keys hm
    modifyContainedASTs f (EquivTracker hm m total) =
        (EquivTracker . HM.fromList . map (\(k, v) -> (f k, v)) $ HM.toList hm) m total

instance ASTContainer EquivTracker Type where
    containedASTs (EquivTracker hm _ _) = containedASTs $ HM.keys hm
    modifyContainedASTs f (EquivTracker hm m total) =
        ( EquivTracker
        . HM.fromList
        . map (\(k, v) -> (modifyContainedASTs f k, modifyContainedASTs f v))
        $ HM.toList hm )
        m total

instance Named EquivTracker where
    names (EquivTracker hm _ _) = names hm
    rename old new (EquivTracker hm m total) =
        EquivTracker (rename old new hm) m total
