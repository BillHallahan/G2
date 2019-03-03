{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Liquid.Types ( LHOutput (..)
                                 , Measures
                                 , LHState (..)
                                 , LHStateM (..)
                                 , ExState (..)
                                 , AnnotMap (..)
                                 , consLHState
                                 , deconsLHState
                                 , measuresM
                                 , assumptionsM
                                 , annotsM
                                 , runLHStateM
                                 , evalLHStateM
                                 , execLHStateM
                                 , lookupMeasure
                                 , lookupMeasureM
                                 , insertMeasureM
                                 , mapMeasuresM
                                 , lookupAssumptionM
                                 , insertAssumptionM
                                 , mapAssumptionsM
                                 , lookupAnnotM
                                 , insertAnnotM
                                 , mapAnnotsExpr
                                 , andM
                                 , orM
                                 , notM
                                 , iffM
                                 , lhTCM
                                 , lhOrdTCM
                                 , lhEqM
                                 , lhNeM
                                 , lhLtM
                                 , lhLeM
                                 , lhGtM
                                 , lhGeM
                                 , lhLtE
                                 , lhLeE
                                 , lhGtE
                                 , lhGeE

                                 , lhPlusM
                                 , lhMinusM
                                 , lhTimesM
                                 , lhDivM
                                 , lhNegateM
                                 , lhModM
                                 , lhFromIntegerM
                                 , lhNumOrdM

                                 , lhAndE
                                 , lhOrE
                                 
                                 , lhPPM ) where

import Data.Coerce
import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Control.Monad.State.Lazy as SM

import qualified G2.Language as L
import qualified G2.Language.ExprEnv as E
import G2.Language.Monad

import G2.Liquid.TCValues

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Constraint.Types
import Language.Fixpoint.Types.Constraints

data LHOutput = LHOutput { ghcI :: GhcInfo
                         , cgI :: CGInfo
                         , solution :: FixSolution }

type Measures = L.ExprEnv

type Assumptions = M.Map L.Name L.Expr

newtype AnnotMap =
    AM { unAnnotMap :: HM.HashMap L.Span [(Maybe T.Text, L.Expr)] }
    deriving (Eq, Show, Read)

-- [LHState]
-- measures is an extra expression environment, used to build Assertions.
-- This distinction between functions for code, and functions for asserts is important because
-- Assertions should not themselves contain assertions.  A measure function
-- may be used both in code and in an assertion, but should only have it's
-- refinement type added in the code
--  
-- Invariant: Internally, functions in the State ExprEnv need to have LH Dict arguments added,
-- (see addLHTCExprEnv) whereas functions in the measures should be created with the LH Dicts
-- already accounted for.


-- | LHState
-- Wraps a State, along with the other information needed to parse
-- LiquidHaskell ASTs
data LHState = LHState { state :: L.State [L.FuncCall]
                       , measures :: Measures
                       , tcvalues :: TCValues
                       , assumptions :: Assumptions
                       , annots :: AnnotMap
                       } deriving (Eq, Show, Read)

consLHState :: L.State [L.FuncCall] -> Measures -> TCValues -> LHState
consLHState s meas tcv =
    LHState { state = s
            , measures = meas
            , tcvalues = tcv
            , assumptions = M.empty
            , annots = AM HM.empty }

deconsLHState :: LHState -> L.State [L.FuncCall]
deconsLHState (LHState { state = s
                       , measures = meas }) =
    s { L.expr_env = E.union (L.expr_env s) meas }

measuresM :: LHStateM Measures
measuresM = do
    (lh_s, _) <- SM.get
    return $ measures lh_s

assumptionsM :: LHStateM Assumptions
assumptionsM = do
    (lh_s, _) <- SM.get
    return $ assumptions lh_s

annotsM :: LHStateM AnnotMap
annotsM = do
    (lh_s, _) <- SM.get
    return $ annots lh_s

newtype LHStateM a = LHStateM { unSM :: (SM.State (LHState, L.Bindings) a) } deriving (Applicative, Functor, Monad)

instance SM.MonadState (LHState, L.Bindings) LHStateM where
    state f = LHStateM (SM.state f) 

instance ExState (LHState, L.Bindings) LHStateM where
    exprEnv = readRecord $ expr_env . fst
    putExprEnv = rep_expr_envM

    typeEnv = readRecord $ type_env . fst
    putTypeEnv = rep_type_envM

    nameGen = readRecord $ name_gen . fst
    -- nameGen = readRecord $ L.name_gen . snd
    putNameGen = rep_name_genM

    knownValues = readRecord $ known_values . fst
    putKnownValues = rep_known_valuesM

    typeClasses = readRecord $ type_classes . fst
    putTypeClasses = rep_type_classesM

instance FullState (LHState, L.Bindings) LHStateM where
    currExpr = readRecord $ curr_expr . fst
    putCurrExpr = rep_curr_exprM

    inputNames = readRecord $ L.input_names . snd
    fixedInputs = readRecord $ L.fixed_inputs . snd

runLHStateM :: LHStateM a -> LHState -> L.Bindings -> (a, (LHState, L.Bindings))
runLHStateM (LHStateM s) lh_s b = SM.runState s (lh_s, b)

evalLHStateM :: LHStateM a -> LHState -> L.Bindings -> a
evalLHStateM s = (\lh_s b -> fst (runLHStateM s lh_s b))

execLHStateM :: LHStateM a -> LHState -> L.Bindings -> (LHState, L.Bindings)
execLHStateM s = (\lh_s b -> snd (runLHStateM s lh_s b))

liftState :: (L.State [L.FuncCall] -> a) -> LHState -> a
liftState f = f . state

name_gen :: LHState -> L.NameGen
name_gen = liftState L.name_gen

expr_env :: LHState -> L.ExprEnv
expr_env = liftState L.expr_env

rep_expr_envM :: L.ExprEnv -> LHStateM ()
rep_expr_envM eenv = do
    (lh_s, b) <- SM.get
    let s = state lh_s
    let s' = s {L.expr_env = eenv}
    SM.put $ (lh_s {state = s'}, b)

type_env :: LHState -> L.TypeEnv
type_env = liftState L.type_env

rep_type_envM :: L.TypeEnv -> LHStateM ()
rep_type_envM tenv = do
    (lh_s, b) <- SM.get
    let s = state lh_s
    let s' = s {L.type_env = tenv}
    SM.put $ (lh_s {state = s'}, b)

rep_name_genM :: L.NameGen -> LHStateM ()
rep_name_genM ng = do
    (lh_s, b) <- SM.get
    let s = state lh_s
    let s' = s {L.name_gen = ng}
    SM.put $ (lh_s {state = s'}, b)
    -- let b' = b {L.name_gen = ng}
    -- SM.put $ (lh_s {state = s}, b')

known_values :: LHState -> L.KnownValues
known_values = liftState L.known_values

rep_known_valuesM :: L.KnownValues -> LHStateM ()
rep_known_valuesM kv = do
    (lh_s, b) <- SM.get
    let s = state lh_s
    let s' = s {L.known_values = kv}
    SM.put $ (lh_s {state = s'}, b)

curr_expr :: LHState -> L.CurrExpr
curr_expr = liftState L.curr_expr

rep_curr_exprM :: L.CurrExpr -> LHStateM ()
rep_curr_exprM ce = do
    (lh_s, b) <- SM.get
    let s = state lh_s
    let s' = s {L.curr_expr = ce}
    SM.put $ (lh_s {state = s'}, b)

type_classes :: LHState -> L.TypeClasses
type_classes = liftState L.type_classes

rep_type_classesM :: L.TypeClasses -> LHStateM ()
rep_type_classesM tc = do
    (lh_s,b) <- SM.get
    let s = state lh_s
    let s' = s {L.type_classes = tc}
    SM.put $ (lh_s {state = s'}, b)

liftLHState :: (LHState -> a) -> LHStateM a
liftLHState f = do
    (lh_s, _) <- SM.get
    return (f lh_s) 

lookupMeasure :: L.Name -> LHState -> Maybe L.Expr
lookupMeasure n = E.lookup n . measures

lookupMeasureM :: L.Name -> LHStateM (Maybe L.Expr)
lookupMeasureM n = liftLHState (lookupMeasure n)

insertMeasureM :: L.Name -> L.Expr -> LHStateM ()
insertMeasureM n e = do
    (lh_s,b) <- SM.get
    let meas = measures lh_s
    let meas' = E.insert n e meas
    SM.put $ (lh_s {measures = meas'}, b)

mapMeasuresM :: (L.Expr -> LHStateM L.Expr) -> LHStateM ()
mapMeasuresM f = do
    (s@(LHState { measures = meas }), b) <- SM.get
    meas' <- E.mapM f meas
    SM.put $ (s { measures = meas' }, b)

lookupAssumptionM :: L.Name -> LHStateM (Maybe L.Expr)
lookupAssumptionM n = liftLHState (M.lookup n . assumptions)

insertAssumptionM :: L.Name -> L.Expr -> LHStateM ()
insertAssumptionM n e = do
    (lh_s, b) <- SM.get
    let assumpt = assumptions lh_s
    let assumpt' = M.insert n e assumpt
    SM.put $ (lh_s {assumptions = assumpt'}, b)

mapAssumptionsM :: (L.Expr -> LHStateM L.Expr) -> LHStateM ()
mapAssumptionsM f = do
    (s@(LHState { assumptions = assumpt }), b) <- SM.get
    assumpt' <- mapM f assumpt
    SM.put $ (s { assumptions = assumpt' },b)

insertAnnotM :: L.Span -> Maybe T.Text -> L.Expr -> LHStateM ()
insertAnnotM spn t e = do
    (s@(LHState { annots = an }),b) <- SM.get
    let an' = AM . HM.insertWith (++) spn [(t, e)] . unAnnotMap $ an
    SM.put $ (s {annots = an'}, b)

lookupAnnotM :: L.Name -> LHStateM (Maybe [(Maybe T.Text, L.Expr)])
lookupAnnotM (L.Name _ _ _ (Just (L.Span {L.start = l}))) =
    return . Just
           . concatMap snd 
           . find (\(L.Span {L.start = l'}, _) -> l == l')
           . HM.toList
           . unAnnotMap
           =<< annotsM
lookupAnnotM _ = return Nothing

mapAnnotsExpr :: (L.Expr -> LHStateM L.Expr) -> LHStateM ()
mapAnnotsExpr f = do
    (lh_s, b) <- SM.get
    annots' <- modifyContainedASTsM f (annots lh_s)
    SM.put $ (lh_s {annots = annots'}, b)

-- | andM
-- The version of 'and' in the measures
andM :: LHStateM L.Expr
andM = do
    m <- measuresM
    return (L.mkAnd m)

-- | orM
-- The version of 'or' in the measures
orM :: LHStateM L.Expr
orM = do
    m <- measuresM
    return (L.mkOr m)

-- | notM
-- The version of 'not' in the measures
notM :: LHStateM L.Expr
notM = do
    m <- measuresM
    return (L.mkNot m)

-- | iffM
-- The version of 'iff' in the measures
iffM :: LHStateM L.Expr
iffM = do
    m <- measuresM
    return (L.mkIff m)

liftTCValues :: (TCValues -> a) -> LHStateM a
liftTCValues f = do
    (lh_s, _) <- SM.get
    return (f (tcvalues lh_s))

lhTCM :: LHStateM L.Name
lhTCM = liftTCValues lhTC

lhNumTCM :: LHStateM L.Name
lhNumTCM = liftTCValues lhNumTC 

lhOrdTCM :: LHStateM L.Name
lhOrdTCM = liftTCValues lhOrdTC 

lhEqM :: LHStateM L.Name
lhEqM = liftTCValues lhEq

lhNeM :: LHStateM L.Name
lhNeM = liftTCValues lhNe

lhLtM :: LHStateM L.Name
lhLtM = liftTCValues lhLt

lhLeM :: LHStateM L.Name
lhLeM = liftTCValues lhLe

lhGtM :: LHStateM L.Name
lhGtM = liftTCValues lhGt

lhGeM :: LHStateM L.Name
lhGeM = liftTCValues lhGe

binT :: LHStateM L.Type
binT = do
    a <- freshIdN L.TYPE
    let tva = L.TyVar a
    ord <- lhOrdTCM
    lh <- lhTCM
    bool <- tyBoolT

    let ord' = L.TyCon ord L.TYPE
    let lh' = L.TyCon lh L.TYPE

    return $ L.TyForAll (L.NamedTyBndr a) 
                    (L.TyFun
                        ord'
                        (L.TyFun
                            lh'
                            (L.TyFun
                                tva
                                (L.TyFun
                                    tva
                                    bool
                                )
                            )
                        )
                    )

lhLtE :: LHStateM L.Id
lhLtE = do
    n <- liftTCValues lhLt
    return . L.Id n =<< binT 

lhLeE :: LHStateM L.Id
lhLeE = do
    n <- liftTCValues lhLe
    return . L.Id n =<< binT 

lhGtE :: LHStateM L.Id
lhGtE = do
    n <- liftTCValues lhGt
    return . L.Id n =<< binT 

lhGeE :: LHStateM L.Id
lhGeE = do
    n <- liftTCValues lhGe
    return . L.Id n =<< binT 


numT :: LHStateM L.Type
numT = do
    a <- freshIdN L.TYPE
    let tva = L.TyVar a
    num <- lhNumTCM

    let num' = L.TyCon num L.TYPE

    return $ L.TyForAll (L.NamedTyBndr a) 
                    (L.TyFun
                        num'
                        (L.TyFun
                            tva
                            tva
                        )
                    )

lhPlusM :: LHStateM L.Name
lhPlusM = liftTCValues lhPlus

lhMinusM :: LHStateM L.Name
lhMinusM = liftTCValues lhMinus

lhTimesM :: LHStateM L.Name
lhTimesM = liftTCValues lhTimes

lhDivM :: LHStateM L.Name
lhDivM = liftTCValues lhDiv

lhNegateM :: LHStateM L.Name
lhNegateM = liftTCValues lhNegate

lhModM :: LHStateM L.Name
lhModM = liftTCValues lhMod

lhFromIntegerM :: LHStateM L.Id
lhFromIntegerM = do
    n <- liftTCValues lhFromInteger
    return . L.Id n =<< numT 

lhNumOrdM :: LHStateM L.Id
lhNumOrdM = do
    num <- lhNumTCM
    let num' = L.TyCon num L.TYPE

    ord <- lhOrdTCM
    let ord' = L.TyCon ord L.TYPE

    n <- liftTCValues lhNumOrd
    return $ L.Id n (L.TyFun num' ord') 

lhPPM :: LHStateM L.Name
lhPPM = liftTCValues lhPP

lhAndE :: LHStateM L.Expr
lhAndE = do
    b <- tyBoolT

    n <- liftTCValues lhAnd
    return $ L.Var (L.Id n (L.TyFun b (L.TyFun b b)))

lhOrE :: LHStateM L.Expr
lhOrE = do
    b <- tyBoolT

    n <- liftTCValues lhOr
    return $ L.Var (L.Id n (L.TyFun b (L.TyFun b b)))

instance L.ASTContainer AnnotMap L.Expr where
    containedASTs =  map snd . concat . HM.elems . unAnnotMap
    modifyContainedASTs f = AM . HM.map (L.modifyContainedASTs f) . coerce

instance L.ASTContainer AnnotMap L.Type where
    containedASTs = L.containedASTs . map snd . concat . HM.elems . unAnnotMap
    modifyContainedASTs f = AM . HM.map (L.modifyContainedASTs f) . coerce

instance ASTContainerM AnnotMap L.Expr where
    modifyContainedASTsM f (AM am) = do
        am' <- mapM (modifyContainedASTsM f) am
        return (AM am')

instance L.Named AnnotMap where
    names = L.names . unAnnotMap
    rename old new = coerce . L.rename old new . unAnnotMap
    renames hm = coerce . L.renames hm . unAnnotMap
