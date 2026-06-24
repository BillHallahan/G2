{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module G2.Language.Monad.Support ( StateT
                                 , StateM
                                 , StateNGT
                                 , StateNG
                                 , NameGenT
                                 , NameGenM
                                 , NamingM (..)
                                 , ExprEnvM (..)
                                 , ExState (..)
                                 , FullState (..)
                                 , runStateM
                                 , execStateM
                                 , runNamingM
                                 , runNamingT
                                 , runExprEnvM
                                 , runStateMInNamingM
                                 , runStateNGT
                                 , runStateNG
                                 , execStateNG
                                 , readRecord
                                 , withNG
                                 , mapCurrExpr
                                 , insertPC
                                 , insertPCStateNG
                                 , getPCStateNG
                                 , putPCStateNG
                                 , mapMAccumB ) where

import Control.Monad.Identity
import qualified Control.Monad.State.Lazy as SM

import G2.Language.Naming
import qualified G2.Language.PathConds as PC
import G2.Language.Syntax
import G2.Language.Support
import G2.Language.TypeClasses

-- | A wrapper for `State`, allowing it to be used as a monadic context.
type StateT t m a = SM.StateT (State t, Bindings) m a
type StateM t a = StateT t Identity a

type StateNGT t m a = SM.StateT (State t, NameGen) m a
type StateNG t a = StateNGT t Identity a

-- | A wrapper for `NameGen`, allowing it to be used as a monadic context.
type NameGenT m a = SM.StateT NameGen m a
type NameGenM a = NameGenT Identity a

-- | A wrapper for `ExprEnv`, allowing it to be used as a monadic context.
type EET m a = SM.StateT ExprEnv m a
type EEM a = EET Identity a

-- instance SM.MonadState (State t, Bindings) (SM.State (State t, Bindings)) where
--     state f = StateM (SM.state f)

-- instance SM.MonadState (State t, NameGen) (SM.State (State t, NameGen)) where
--     state f = StateNG (SM.state f)

-- instance SM.MonadState NameGen (SM.State NameGen) where
--     state f = NameGenM (SM.state f)

-- We split the State Monad into two pieces, so we can use it in the
-- initialization stage of G2 (in this stage, we do not have an entire State.
-- See G2.Initialization.Types), or so that we can just use it with smaller
-- pieces of a state.

class Monad m => NamingM s m | m -> s where
    nameGen :: m NameGen
    putNameGen :: NameGen -> m ()

class Monad m => ExprEnvM s m | m -> s where
    exprEnv :: m ExprEnv
    putExprEnv :: ExprEnv -> m ()

-- | Allows access to certain basic components of a state.
class (ExprEnvM s m, NamingM s m) => ExState s m | m -> s where
    typeEnv :: m TypeEnv
    tyVarEnv :: m TyVarEnv
    putTypeEnv :: TypeEnv -> m ()

    knownValues :: m KnownValues
    putKnownValues :: KnownValues -> m ()

    typeClasses :: m TypeClasses
    putTypeClasses :: TypeClasses -> m ()

-- Extends `ExState`, allowing access to a more complete set of the
-- components in the `State`.
class ExState s m => FullState s m | m -> s where
    currExpr :: m CurrExpr
    putCurrExpr :: CurrExpr -> m ()

    pathConds :: m PathConds
    putPathConds :: PathConds -> m ()

    nonRedPathConds :: m NonRedPathConds
    putNonRedPathConds :: NonRedPathConds -> m ()

    inputNames :: m [Name]
    fixedInputs :: m [Expr]

instance Monad m => NamingM NameGen (SM.StateT NameGen m) where
    nameGen = SM.get
    putNameGen = SM.put

instance Monad m => NamingM (State t, Bindings) (SM.StateT (State t, Bindings) m) where
    nameGen = readRecord (\(_, b) -> name_gen b)
    putNameGen = rep_name_genM

instance Monad m => NamingM (State t, NameGen) (SM.StateT (State t, NameGen) m) where
    nameGen = readRecord (\(_, ng) -> ng)
    putNameGen = rep_name_genNG

instance Monad m => ExprEnvM (State t, Bindings) (SM.StateT (State t, Bindings) m) where
    exprEnv = readRecord (\(s, _) -> expr_env s)
    putExprEnv = rep_expr_envM

instance Monad m => ExprEnvM (State t, NameGen) (SM.StateT (State t, NameGen) m) where
    exprEnv = readRecord (\(s, _) -> expr_env s)
    putExprEnv = rep_expr_envNG

instance Monad m => ExState (State t, Bindings) (SM.StateT (State t, Bindings) m) where
    typeEnv = readRecord (\(s, _) -> type_env s)
    putTypeEnv = rep_type_envM

    knownValues = readRecord (\(s, _) -> known_values s)
    putKnownValues = rep_known_valuesM

    typeClasses = readRecord (\(s, _) -> type_classes s)
    putTypeClasses = rep_type_classesM

    tyVarEnv = readRecord (\(s, _) -> tyvar_env s)

instance Monad m => ExState (State t, NameGen) (SM.StateT (State t, NameGen) m) where
    typeEnv = readRecord (\(s, _) -> type_env s)
    putTypeEnv = rep_type_envNG

    knownValues = readRecord (\(s, _) -> known_values s)
    putKnownValues = rep_known_valuesNG

    typeClasses = readRecord (\(s, _) -> type_classes s)
    putTypeClasses = rep_type_classesNG

    tyVarEnv = readRecord (\(s, _) -> tyvar_env s)

instance Monad m => FullState (State t, Bindings) (SM.StateT (State t, Bindings) m) where
    currExpr = readRecord (\(s, _) -> curr_expr s)
    putCurrExpr = rep_curr_exprM

    pathConds = readRecord (\(s, _) -> path_conds s)
    putPathConds = rep_path_condsM

    nonRedPathConds = readRecord (\(s, _) -> non_red_path_conds s)
    putNonRedPathConds = rep_nonRedM


    inputNames = readRecord (\(_, b) -> input_names b)
    fixedInputs = readRecord (\(_,b) -> fixed_inputs b)


runStateM :: StateM t a -> State t -> Bindings -> (a, (State t, Bindings))
runStateM s s' b = SM.runState s (s', b)

execStateM :: StateM t a -> State t -> Bindings -> (State t, Bindings)
execStateM s = (\lh_s b -> snd (runStateM s lh_s b))

runStateNGT :: StateNGT t m a -> State t -> NameGen -> m (a, (State t, NameGen))
runStateNGT s s' ng = SM.runStateT s (s', ng)

runStateNG :: StateNG t a -> State t -> NameGen -> (a, (State t, NameGen))
runStateNG s s' ng = SM.runState s (s', ng)

execStateNG :: StateNG t a -> State t -> NameGen -> (State t, NameGen)
execStateNG s = (\lh_s ng -> snd (runStateNG s lh_s ng))

runNamingT :: NameGenT m a -> NameGen -> m (a, NameGen)
runNamingT s = SM.runStateT s

runNamingM :: NameGenM a -> NameGen -> (a, NameGen)
runNamingM s = SM.runState s

runExprEnvM :: EEM a -> ExprEnv -> (a, ExprEnv)
runExprEnvM s = SM.runState s

runStateMInNamingM :: (Monad m, NamingM s m) => StateNG t a -> State t -> m (a, State t)
runStateMInNamingM m s = do
    ng <- nameGen
    let (a, (s', ng')) = runStateNG m s ng
    putNameGen ng'
    return (a, s')

readRecord :: SM.MonadState s m => (s -> r) -> m r
readRecord f = return . f =<< SM.get

rep_expr_envM :: Monad m => ExprEnv -> StateT t m ()
rep_expr_envM eenv = do
    (s,b) <- SM.get
    SM.put $ (s {expr_env = eenv}, b)

rep_expr_envNG :: Monad m => ExprEnv -> StateNGT t m ()
rep_expr_envNG eenv = do
    (s,b) <- SM.get
    SM.put $ (s {expr_env = eenv}, b)

rep_type_envM :: Monad m => TypeEnv -> StateT t m ()
rep_type_envM tenv = do
    (s,b) <- SM.get
    SM.put $ (s {type_env = tenv}, b)

rep_type_envNG :: Monad m => TypeEnv -> StateNGT t m ()
rep_type_envNG tenv = do
    (s,b) <- SM.get
    SM.put $ (s {type_env = tenv}, b)

withNG :: NamingM s m => (NameGen -> (a, NameGen)) -> m a
withNG f = do
    ng <- nameGen
    let (a, ng') = f ng
    putNameGen ng'
    return a

rep_name_genM :: Monad m => NameGen -> StateT t m ()
rep_name_genM ng = do
    (s,b) <- SM.get
    SM.put $ (s, b {name_gen = ng})

rep_name_genNG :: Monad m => NameGen -> StateNGT t m ()
rep_name_genNG ng = do
    (s, _) <- SM.get
    SM.put $ (s, ng)

rep_known_valuesM :: Monad m => KnownValues -> StateT t m ()
rep_known_valuesM kv = do
    (s, b) <- SM.get
    SM.put $ (s {known_values = kv}, b)

rep_known_valuesNG :: Monad m => KnownValues -> StateNGT t m ()
rep_known_valuesNG kv = do
    (s, b) <- SM.get
    SM.put $ (s {known_values = kv}, b)


rep_type_classesM :: Monad m => TypeClasses -> StateT t m ()
rep_type_classesM tc = do
    (s, b) <- SM.get
    SM.put $ (s {type_classes = tc}, b)

rep_type_classesNG :: Monad m => TypeClasses -> StateNGT t m ()
rep_type_classesNG tc = do
    (s, b) <- SM.get
    SM.put $ (s {type_classes = tc}, b)

rep_curr_exprM :: Monad m => CurrExpr -> StateT t m ()
rep_curr_exprM ce = do
    (s, b) <- SM.get
    SM.put $ (s {curr_expr = ce}, b)

rep_nonRedM :: Monad m => NonRedPathConds -> StateT t m ()
rep_nonRedM nrpc = do
    (s, b) <- SM.get
    SM.put $ (s {non_red_path_conds = nrpc}, b)

mapCurrExpr :: FullState s m => (Expr -> m Expr) -> m ()
mapCurrExpr f = do
    (CurrExpr er e) <- currExpr
    e' <- f e
    putCurrExpr (CurrExpr er e') 

rep_path_condsM :: Monad m => PathConds -> StateT t m ()
rep_path_condsM pc = do
    (s, b) <- SM.get
    SM.put $ (s {path_conds = pc}, b)

insertPC :: FullState s m => PathCond -> m ()
insertPC pc = do
    pcs <- pathConds
    putPathConds $ PC.insert pc pcs 

getPCStateNG :: Monad m => StateNGT t m PathConds
getPCStateNG = do
    ((State { path_conds = pcs }), _) <- SM.get
    return pcs

putPCStateNG :: Monad m => PathConds -> StateNGT t m ()
putPCStateNG pcs = do
    (s, ng) <- SM.get
    SM.put (s { path_conds = pcs }, ng)


insertPCStateNG :: Monad m => PathCond -> StateNGT t m ()
insertPCStateNG pc = do
    (s@(State { path_conds = pcs }), ng) <- SM.get
    SM.put (s { path_conds = PC.insert pc pcs}, ng)

mapMAccumB :: Monad m => (a -> b -> m (a, c)) -> a -> [b] -> m (a, [c])
mapMAccumB _ a [] = do
    return (a, [])
mapMAccumB f a (x:xs) = do
    (a', res) <- f a x
    (a'', res2) <- mapMAccumB f a' xs
    return $ (a'', res:res2)
