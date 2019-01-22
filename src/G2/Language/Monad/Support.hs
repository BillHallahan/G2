{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Language.Monad.Support ( StateM
                                 , ExState (..)
                                 , FullState (..)
                                 , runStateM
                                 , readRecord
                                 , withNG
                                 , mapCurrExpr ) where

import qualified Control.Monad.State.Lazy as SM

import G2.Language.Naming
import G2.Language.Syntax
import G2.Language.Support
import G2.Language.TypeClasses

-- | A wrapper for `State`, allowing it to be used as a monadic context.
newtype StateM t a = StateM (SM.State (State t, Bindings) a) deriving (Applicative, Functor, Monad)

instance SM.MonadState (State t, Bindings) (StateM t) where
    state f = StateM (SM.state f)

-- We split the State Monad into two pieces, so we can use it in the
-- initialization stage of G2. In this stage, we do not have an entire State.
-- See G2.Initialization.Types

-- | Allows access to certain basic components of a state.
class SM.MonadState s m => ExState s m | m -> s where
    exprEnv :: m ExprEnv
    putExprEnv :: ExprEnv -> m ()

    typeEnv :: m TypeEnv
    putTypeEnv :: TypeEnv -> m ()

    nameGen :: m NameGen
    putNameGen :: NameGen -> m ()

    knownValues :: m KnownValues
    putKnownValues :: KnownValues -> m ()

    typeClasses :: m TypeClasses
    putTypeClasses :: TypeClasses -> m ()

-- Extends `ExState`, allowing access to a more complete set of the
-- components in the `State`.
class ExState s m => FullState s m | m -> s where
    currExpr :: m CurrExpr
    putCurrExpr :: CurrExpr -> m ()

    inputIds :: m InputIds
    fixedInputs :: m [Expr]

instance ExState (State t, Bindings) (StateM t) where
    exprEnv = readRecord (\(s, b) -> expr_env s)
    putExprEnv = rep_expr_envM

    typeEnv = readRecord (\(s, b) -> type_env s)
    putTypeEnv = rep_type_envM

    nameGen = readRecord (\(s, b) -> name_gen s)
    putNameGen = rep_name_genM

    knownValues = readRecord (\(s, b) -> known_values s)
    putKnownValues = rep_known_valuesM

    typeClasses = readRecord (\(s, b) -> type_classes s)
    putTypeClasses = rep_type_classesM

instance FullState (State t, Bindings) (StateM t) where
    currExpr = readRecord (\(s, b) -> curr_expr s)
    putCurrExpr = rep_curr_exprM

    inputIds = readRecord (\(s, b) -> input_ids s)
    fixedInputs = readRecord (\(s,b) -> fixed_inputs b)

runStateM :: StateM t a -> State t -> Bindings -> (a, (State t, Bindings))
runStateM (StateM s) s' b = SM.runState s (s', b)

readRecord :: SM.MonadState s m => (s -> r) -> m r
readRecord f = return . f =<< SM.get

-- f =<< SM.get = do
    -- x <- SM.get -- (s,b)
    --f (s,b)

rep_expr_envM :: ExprEnv -> StateM t ()
rep_expr_envM eenv = do
    (s,b) <- SM.get
    SM.put $ (s {expr_env = eenv}, b)

rep_type_envM :: TypeEnv -> StateM t ()
rep_type_envM tenv = do
    (s,b) <- SM.get
    SM.put $ (s {type_env = tenv}, b)

withNG :: ExState s m => (NameGen -> (a, NameGen)) -> m a
withNG f = do
    ng <- nameGen
    let (a, ng') = f ng
    putNameGen ng'
    return a

rep_name_genM :: NameGen -> StateM t ()
rep_name_genM ng = do
    (s,b) <- SM.get
    SM.put $ (s {name_gen = ng}, b)

rep_known_valuesM :: KnownValues -> StateM t ()
rep_known_valuesM kv = do
    (s, b) <- SM.get
    SM.put $ (s {known_values = kv}, b)

rep_type_classesM :: TypeClasses -> StateM t ()
rep_type_classesM tc = do
    (s, b) <- SM.get
    SM.put $ (s {type_classes = tc}, b)

rep_curr_exprM :: CurrExpr -> StateM t ()
rep_curr_exprM ce = do
    (s, b) <- SM.get
    SM.put $ (s {curr_expr = ce}, b)

mapCurrExpr :: FullState s m => (Expr -> m Expr) -> m ()
mapCurrExpr f = do
    (CurrExpr er e) <- currExpr
    e' <- f e
    putCurrExpr (CurrExpr er e') 
