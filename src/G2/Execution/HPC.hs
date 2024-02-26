{-# Language FlexibleContexts, FlexibleInstances, GeneralisedNewtypeDeriving,
             MultiParamTypeClasses, StandaloneDeriving #-}

-- | Provides infrastructure to track which HPC ticks have been encountered during symbolic execution.
module G2.Execution.HPC ( HpcT
                        , HpcM
                        
                        , hpcReducer) where

import G2.Execution.Reducer
import G2.Language

import Control.Monad.Identity
import qualified Control.Monad.State.Lazy as SM
import qualified Data.HashSet as HS
import Data.Monoid
import qualified Data.Text as T

newtype HpcT m a = HpcT (SM.StateT (HS.HashSet (Int, T.Text)) m a) deriving (Functor, Applicative, Monad)

deriving instance Monad m => (SM.MonadState (HS.HashSet (Int, T.Text)) (HpcT m))

type HpcM a = HpcT Identity a

hpcReducer :: SM.MonadState (HS.HashSet (Int, T.Text)) m =>
              State t -> -- ^ The initial state being symbolically executed
              Reducer m () t
hpcReducer init_state =
    let
        hpc_tick_num = evalASTs countHPCTicks (expr_env init_state)
    in
    mkSimpleReducer (const ()) logTick
    where
        logTick _ s@(State {curr_expr = CurrExpr _ (Tick (HpcTick i m) _)}) b = do
            SM.modify (HS.insert (i, m))
            return (NoProgress, [(s, ())], b)
        logTick _ s b = return (NoProgress, [(s, ())], b)

countHPCTicks :: Expr -> Sum Int
countHPCTicks (Tick (HpcTick _ _) _) = Sum 1
countHPCTicks _ = 0