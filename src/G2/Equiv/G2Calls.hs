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

-- get names from symbolic ids in the state
runG2ForRewriteV :: StateET -> Config -> Bindings -> IO ([ExecRes EquivTracker], Bindings)
runG2ForRewriteV state config bindings = do
    SomeSolver solver <- initSolver config
    let simplifier = IdSimplifier
        sym_ids = symbolic_ids state
        sym_names = map idName sym_ids
        sym_config = addSearchNames (names $ track state)
                   $ addSearchNames (input_names bindings) emptyMemConfig

        state' = state { track = (track state) { saw_tick = Nothing } }

    (in_out, bindings') <- case rewriteRedHaltOrd solver simplifier config of
                (red, hal, ord) ->
                    runG2WithSomes red hal ord solver simplifier sym_config state' bindings

    close solver

    return (in_out, bindings')

rewriteRedHaltOrd :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> Config -> (SomeReducer EquivTracker, SomeHalter EquivTracker, SomeOrderer EquivTracker)
rewriteRedHaltOrd solver simplifier config =
    let
        share = sharing config

        tr_ng = mkNameGen ()
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

data EnforceProgress = EnforceProgress

data EnforceProgressR = EnforceProgressR

data EnforceProgressH = EnforceProgressH

instance Reducer EnforceProgressR () EquivTracker where
    initReducer _ _ = ()
    redRules r rv s@(State { curr_expr = CurrExpr _ e
                           , num_steps = n
                           , track = EquivTracker et m })
                  b =
        let s' = s { track = EquivTracker et (Just n) }
        in
        case (e, m) of
            (Tick (NamedLoc (Name p _ _ _)) _, Nothing) ->
                if p == T.pack "STACK"
                then return (InProgress, [(s', ())], b, r)
                else return (NoProgress, [(s, ())], b, r)
            -- TODO condense these into one case?
            -- TODO n > n0 + 1
            -- then again, it might not matter at all here
            (Tick (NamedLoc (Name p _ _ _)) _, Just n0) ->
                if p == T.pack "STACK" && n > n0 + 1
                then return (InProgress, [(s', ())], b, r)
                else return (NoProgress, [(s, ())], b, r)
            _ -> return (NoProgress, [(s, rv)], b, r)

-- TODO delete GuardedHalter code
argCount :: Type -> Int
argCount = length . spArgumentTypes . PresType

exprFullApp :: ExprEnv -> Expr -> Bool
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
<<<<<<< HEAD
                , not (isVar e') = length (unApp e) == 1 + argCount t && argCount t > 0
=======
                , not (isVar e')
                , c_unapp <- length (unApp e)
                , c_unapp >= 2 = c_unapp == 1 + argCount t
>>>>>>> 75137e870a6edc897b0e8834707389853e259c94
exprFullApp _ _ = False

isVar :: Expr -> Bool
isVar (Var _) = True
isVar _ = False

-- TODO changed t to EquivTracker
instance Halter EnforceProgressH () EquivTracker where
    initHalt _ _ = ()
    updatePerStateHalt _ _ _ _ = ()
    stopRed _ _ _ s =
        let CurrExpr _ e = curr_expr s
            n' = num_steps s
            EquivTracker _ m = track s
            h = expr_env s
        in
        case m of
            Nothing -> return Continue
            -- Execution needs to take strictly more than one step beyond the
            -- point when it reaches the Tick because the act of unwrapping the
            -- expression inside the Tick counts as one step.
            Just n0 -> do
<<<<<<< HEAD
                {-
                case unApp e of
                    (Var (Id n t)):_ ->
                        putStrLn $ "stopRed\nE.lookup n h = " ++ show (E.lookup n h)
                                    ++ "\nexprFullApp = " ++ show (exprFullApp h e)
                                    ++ "\nargCount t = " ++ show (argCount t)
                                    ++ "\nlength (unApp e) = " ++ show (length (unApp e))
                    _ -> return ()
                -}
=======
>>>>>>> 75137e870a6edc897b0e8834707389853e259c94
                if (isExecValueForm s) || (exprFullApp h e)
                       then return (if n' > n0 + 1 then Accept else Continue)
                       else return Continue
    stepHalter _ _ _ _ _ = ()

-- Maps higher order function calles to symbolic replacements.
-- This allows the same call to be replaced by the same Id consistently.
data EquivTracker = EquivTracker { higher_order :: HM.HashMap Expr Id, saw_tick :: Maybe Int } deriving Show

emptyEquivTracker :: EquivTracker
emptyEquivTracker = EquivTracker HM.empty Nothing

data EquivReducer = EquivReducer

-- TODO new variable m
instance Reducer EquivReducer () EquivTracker where
    initReducer _ _ = ()
    redRules r _ s@(State { expr_env = eenv
                          , curr_expr = CurrExpr Evaluate e
                          , symbolic_ids = symbs
                          , track = EquivTracker et m })
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
                        s' = s { curr_expr = CurrExpr Evaluate (Var v)
                               , track = EquivTracker et' m
                               , expr_env = E.insertSymbolic (idName v) v eenv
                               , symbolic_ids = v:symbs }
                        b' = b { name_gen = ng' }
                    in
                    return (InProgress, [(s', ())], b', r)
    redRules r rv s b = return (NoProgress, [(s, rv)], b, r)

isSymFuncApp :: ExprEnv -> Expr -> Bool
isSymFuncApp eenv e
    | v@(Var _):es@(_:_) <- unApp e
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

-- TODO not all m usage here and elsewhere may be correct
instance ASTContainer EquivTracker Expr where
    containedASTs (EquivTracker hm _) = HM.keys hm
    modifyContainedASTs f (EquivTracker hm m) =
        (EquivTracker . HM.fromList . map (\(k, v) -> (f k, v)) $ HM.toList hm) m

instance ASTContainer EquivTracker Type where
    containedASTs (EquivTracker hm _) = containedASTs $ HM.keys hm
    modifyContainedASTs f (EquivTracker hm m) =
        ( EquivTracker
        . HM.fromList
        . map (\(k, v) -> (modifyContainedASTs f k, modifyContainedASTs f v))
        $ HM.toList hm )
        m

instance Named EquivTracker where
    names (EquivTracker hm _) = names hm
    rename old new (EquivTracker hm m) = EquivTracker (rename old new hm) m
