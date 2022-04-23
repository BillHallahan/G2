{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

module G2.Liquid.Types ( LHOutput (..)
                       , CounterExample (..)
                       , Measures
                       , LHState (..)
                       , LHStateM (..)
                       , NamingM (..)
                       , ExState (..)
                       , AnnotMap (..)
                       , Abstracted (..)
                       , AbstractedInfo (..)
                       , Assumptions
                       , Posts
                       , TyVarBags
                       , InstFuncs

                       -- For compatibility with new LH versions
                      #if MIN_VERSION_liquidhaskell(0,8,10)
                       , GhcInfo, GhcSrc, GhcSpec
                       , pattern GI, giSpec, giSrc
                       , pattern SP, gsSig, gsData, gsQual, gsVars, gsTerm
                       , pattern Src, giTarget, giCbs, giDefVars
                      #endif

                       , tcValuesM

                       , mapAbstractedFCs
                       , mapAbstractedInfoFCs
                       , consLHState
                       , deconsLHState
                       , measuresM
                       , lhRenamedTCM
                       , assumptionsM
                       , postsM
                       , annotsM
                       , tyVarBagsM
                       , runLHStateM
                       , evalLHStateM
                       , execLHStateM
                       , lookupMeasure
                       , lookupMeasureM
                       , insertMeasureM
                       , mapMeasuresM
                       , putMeasuresM
                       , lookupAssumptionM
                       , insertAssumptionM
                       , mapAssumptionsM
                       , lookupPostM
                       , insertPostM
                       , mapPostM
                       , lookupAnnotM
                       , insertAnnotM
                       , mapAnnotsExpr
                       , lookupRenamedTCDict
                       , insertTyVarBags
                       , lookupTyVarBags
                       , setTyVarBags
                       , getTyVarBags
                       , insertInstFuncs
                       , lookupInstFuncs
                       , setInstFuncs
                       , getInstFuncs

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
                       , lhToIntegerM

                       , lhFromRationalM

                       , lhToRatioFuncM
                       
                       , lhNumTCM
                       , lhNumOrdM

                       , lhAndE
                       , lhOrE
                       
                       , lhPPM
                       , lhOrdM ) where

import Data.Coerce
import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Control.Monad.State.Lazy as SM

import qualified G2.Language as L
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.KnownValues as KV
import G2.Language.Monad
import G2.Language.TypeClasses

import G2.Liquid.TCValues

#if MIN_VERSION_liquidhaskell(0,8,10)
import qualified Language.Haskell.Liquid.Types as LT (TargetInfo (..), TargetSrc (..), TargetSpec (..))
#else
import Language.Haskell.Liquid.Types (GhcInfo)
#endif

import Language.Haskell.Liquid.Constraint.Types
import Language.Fixpoint.Types.Constraints

-- LiquidHaskell renamed these types.
-- This preserves compatibility with the old version of LiquidHaskell, and the new versions of LiquidHaskell.
#if MIN_VERSION_liquidhaskell(0,8,10)
type GhcInfo = LT.TargetInfo
type GhcSrc = LT.TargetSrc
type GhcSpec= LT.TargetSpec

pattern GI{giSrc,giSpec} = LT.TargetInfo giSrc giSpec


pattern Src
  { giIncDir
  , giTarget
  , giTargetMod
  , giCbs
  , gsTcs
  , gsCls
  , giDerVars
  , giImpVars
  , giDefVars
  , giUseVars
  , gsExports
  , gsFiTcs
  , gsFiDcs
  , gsPrimTcs
  , gsQualImps
  , gsAllImps
  , gsTyThings
  } = LT.TargetSrc giIncDir giTarget giTargetMod giCbs gsTcs gsCls giDerVars giImpVars
                   giDefVars giUseVars gsExports gsFiTcs gsFiDcs gsPrimTcs gsQualImps
                   gsAllImps gsTyThings




pattern SP 
  { gsSig
  , gsQual
  , gsData
  , gsName
  , gsVars
  , gsTerm
  , gsRefl
  , gsLaws
  , gsImps        
  , gsConfig                  
  } = LT.TargetSpec gsSig gsQual gsData gsName gsVars gsTerm gsRefl gsLaws gsImps gsConfig                  

#endif

data LHOutput = LHOutput { ghcI :: GhcInfo
                         , cgI :: CGInfo
                         , solution :: FixSolution }

data CounterExample = DirectCounter Abstracted [Abstracted]
                    | CallsCounter Abstracted -- ^ The caller, abstracted result
                                   Abstracted -- ^ The callee
                                   [Abstracted]
                    deriving (Eq, Show, Read)

type Measures = L.ExprEnv

type Assumptions = M.Map L.Name L.Expr
type Posts = M.Map L.Name L.Expr

newtype AnnotMap =
    AM { unAnnotMap :: HM.HashMap L.Span [(Maybe T.Text, L.Expr)] }
    deriving (Eq, Show, Read)

-- Abstracted values
data Abstracted = Abstracted { abstract :: L.FuncCall
                             , real :: L.FuncCall
                             , hits_lib_err_in_real :: Bool
                             , func_calls_in_real :: [L.FuncCall] }
                             deriving (Eq, Show, Read)

data AbstractedInfo = AbstractedInfo { init_call :: Abstracted
                                     , abs_violated :: Maybe Abstracted
                                     , abs_calls :: [Abstracted]
                                     , ai_all_calls :: [L.FuncCall] }

mapAbstractedFCs :: (L.FuncCall -> L.FuncCall) ->  Abstracted -> Abstracted
mapAbstractedFCs f (Abstracted { abstract = a
                               , real = r
                               , hits_lib_err_in_real = err
                               , func_calls_in_real = fcr }) =
    Abstracted { abstract = f a
               , real = f r
               , hits_lib_err_in_real = err
               , func_calls_in_real = map f fcr}

mapAbstractedInfoFCs :: (L.FuncCall -> L.FuncCall) ->  AbstractedInfo -> AbstractedInfo
mapAbstractedInfoFCs f (AbstractedInfo { init_call = ic, abs_violated = av, abs_calls = ac, ai_all_calls= allc}) =
    AbstractedInfo { init_call = mapAbstractedFCs f ic
                   , abs_violated = fmap (mapAbstractedFCs f) av
                   , abs_calls = map (mapAbstractedFCs f) ac
                   , ai_all_calls = map f allc }

instance L.ASTContainer Abstracted L.Expr where
    containedASTs ab = L.containedASTs (abstract ab) ++ L.containedASTs (real ab)
    modifyContainedASTs f (Abstracted { abstract = a, real = r, hits_lib_err_in_real = err }) =
        Abstracted { abstract = L.modifyContainedASTs f a
                   , real = L.modifyContainedASTs f r
                   , hits_lib_err_in_real = err}

instance L.ASTContainer Abstracted L.Type where
    containedASTs ab = L.containedASTs (abstract ab) ++ L.containedASTs (real ab)
    modifyContainedASTs f (Abstracted { abstract = a, real = r, hits_lib_err_in_real = err }) =
        Abstracted { abstract = L.modifyContainedASTs f a
                   , real = L.modifyContainedASTs f r
                   , hits_lib_err_in_real = err }

-- | See G2.Liquid.TyVarBags
type TyVarBags = M.Map L.Name [L.Id]
type InstFuncs = M.Map L.Name L.Id

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
                       , lh_tcs :: L.TypeClasses
                       , tcvalues :: TCValues
                       , assumptions :: Assumptions
                       , posts :: Posts
                       , annots :: AnnotMap
                       , tyvar_bags :: TyVarBags
                       , inst_funcs :: InstFuncs
                       } deriving (Eq, Show, Read)

consLHState :: L.State [L.FuncCall] -> Measures -> L.TypeClasses -> TCValues -> LHState
consLHState s meas tc tcv =
    LHState { state = s
            , measures = meas
            , lh_tcs = tc
            , tcvalues = tcv
            , assumptions = M.empty
            , posts = M.empty
            , annots = AM HM.empty
            , tyvar_bags = M.empty
            , inst_funcs = M.empty }

deconsLHState :: LHState -> L.State [L.FuncCall]
deconsLHState (LHState { state = s
                       , measures = meas }) =
    s { L.expr_env = E.union (L.expr_env s) meas }

measuresM :: LHStateM Measures
measuresM = do
    (lh_s, _) <- SM.get
    return $ measures lh_s

lhRenamedTCM :: LHStateM L.TypeClasses
lhRenamedTCM = do
    (lh_s, _) <- SM.get
    return $ lh_tcs lh_s

assumptionsM :: LHStateM Assumptions
assumptionsM = do
    (lh_s, _) <- SM.get
    return $ assumptions lh_s

postsM :: LHStateM Posts
postsM = do
    (lh_s, _) <- SM.get
    return $ posts lh_s

annotsM :: LHStateM AnnotMap
annotsM = do
    (lh_s, _) <- SM.get
    return $ annots lh_s

tyVarBagsM :: LHStateM TyVarBags
tyVarBagsM = do
    (lh_s, _) <- SM.get
    return $ tyvar_bags lh_s


newtype LHStateM a = LHStateM { unSM :: (SM.State (LHState, L.Bindings) a) } deriving (Applicative, Functor, Monad)

instance SM.MonadState (LHState, L.Bindings) LHStateM where
    state f = LHStateM (SM.state f) 

instance NamingM (LHState, L.Bindings) LHStateM where
    nameGen = readRecord $ L.name_gen . snd
    putNameGen = rep_name_genM

instance ExprEnvM (LHState, L.Bindings) LHStateM where
    exprEnv = readRecord $ expr_env . fst
    putExprEnv = rep_expr_envM

instance ExState (LHState, L.Bindings) LHStateM where
    typeEnv = readRecord $ type_env . fst
    putTypeEnv = rep_type_envM

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
    let b' = b {L.name_gen = ng}
    SM.put $ (lh_s {state = s}, b')

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

putMeasuresM :: Measures -> LHStateM ()
putMeasuresM meas = do
    (s, b) <- SM.get
    SM.put $ (s { measures = meas }, b)

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

lookupPostM :: L.Name -> LHStateM (Maybe L.Expr)
lookupPostM n = liftLHState (M.lookup n . posts)

insertPostM :: L.Name -> L.Expr -> LHStateM ()
insertPostM n e = do
    (lh_s, b) <- SM.get
    let pst = posts lh_s
    let pst' = M.insert n e pst
    SM.put $ (lh_s {posts = pst'}, b)

mapPostM :: (L.Expr -> LHStateM L.Expr) -> LHStateM ()
mapPostM f = do
    (s@(LHState { posts = pst }), b) <- SM.get
    pst' <- mapM f pst
    SM.put $ (s { posts = pst' },b)

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

lookupRenamedTCDict :: L.Name -> L.Type -> LHStateM (Maybe L.Id)
lookupRenamedTCDict n t = do
    tc <- lhRenamedTCM
    return $ lookupTCDict tc n t

insertTyVarBags :: L.Name -> [L.Id] -> LHStateM ()
insertTyVarBags n is = do
    (lh_s, b) <- SM.get
    let tyvar_bags' = M.insert n is (tyvar_bags lh_s)
    SM.put $ (lh_s {tyvar_bags = tyvar_bags'}, b)

lookupTyVarBags :: L.Name -> LHStateM (Maybe [L.Id])
lookupTyVarBags n = do
    (lh_s, b) <- SM.get
    return $ M.lookup n (tyvar_bags lh_s)

setTyVarBags :: TyVarBags -> LHStateM ()
setTyVarBags m = do
    (lh_s, b) <- SM.get
    SM.put (lh_s {tyvar_bags = m}, b)

getTyVarBags :: LHStateM TyVarBags
getTyVarBags = return . tyvar_bags . fst =<< SM.get

insertInstFuncs :: L.Name -> L.Id -> LHStateM ()
insertInstFuncs n i = do
    (lh_s, b) <- SM.get
    let inst_funcs' = M.insert n i (inst_funcs lh_s)
    SM.put $ (lh_s {inst_funcs = inst_funcs'}, b)

lookupInstFuncs :: L.Name -> LHStateM (Maybe L.Id)
lookupInstFuncs n = do
    (lh_s, b) <- SM.get
    return $ M.lookup n (inst_funcs lh_s)

setInstFuncs :: M.Map L.Name L.Id -> LHStateM ()
setInstFuncs m = do
    (lh_s, b) <- SM.get
    SM.put (lh_s {inst_funcs = m}, b)

getInstFuncs :: LHStateM InstFuncs
getInstFuncs = return . inst_funcs . fst =<< SM.get

-- | andM
-- The version of 'and' in the measures
andM :: LHStateM L.Expr
andM = do
    m <- measuresM
    n <- lhAndM
    return (m E.! n)

-- | orM
-- The version of 'or' in the measures
orM :: LHStateM L.Expr
orM = do
    m <- measuresM
    n <- lhOrM
    return (m E.! n)

-- | notM
-- The version of 'not' in the measures
notM :: LHStateM L.Expr
notM = do
    m <- measuresM
    n <- lhNotM
    return (m E.! n)

-- | iffM
-- The version of 'iff' in the measures
iffM :: LHStateM L.Expr
iffM = do
    m <- measuresM
    n <- lhIffM
    return (m E.! n)

tcValuesM :: LHStateM TCValues
tcValuesM = liftTCValues id

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

lhAndM :: LHStateM L.Name
lhAndM = liftTCValues lhAnd

lhOrM :: LHStateM L.Name
lhOrM = liftTCValues lhOr

lhNotM :: LHStateM L.Name
lhNotM = liftTCValues lhNot

lhIffM :: LHStateM L.Name
lhIffM = liftTCValues lhIff

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

numT :: LHStateM L.Type
numT = do
    a <- freshIdN L.TYPE
    let tva = L.TyVar a
    num <- lhNumTCM
    integerT <- tyIntegerT

    let num' = L.TyCon num L.TYPE

    return $ L.TyForAll (L.NamedTyBndr a) 
                    (L.TyFun
                        num'
                        (L.TyFun
                            integerT
                            tva
                        )
                    )

lhToRatioFuncM :: LHStateM L.Id
lhToRatioFuncM = do
    n <- liftTCValues lhToRatioFunc
    return . L.Id n =<< ratioFuncT 

ratioFuncT :: LHStateM L.Type
ratioFuncT = do
    a <- freshIdN L.TYPE
    let tva = L.TyVar a
    integral <- return . KV.integralTC =<< knownValues
    integerT <- tyIntegerT

    let integral' = L.TyCon integral L.TYPE

    return $ L.TyForAll (L.NamedTyBndr a) 
                    (L.TyFun
                        integral'
                        (L.TyFun
                            tva
                            (L.TyFun
                              tva
                              L.TyUnknown)
                        )
                    )

lhToIntegerM :: LHStateM L.Id
lhToIntegerM = do
    n <- liftTCValues lhToInteger
    return . L.Id n =<< integralT 

integralT :: LHStateM L.Type
integralT = do
    a <- freshIdN L.TYPE
    let tva = L.TyVar a
    integral <- return . KV.integralTC =<< knownValues
    integerT <- tyIntegerT

    let integral' = L.TyCon integral L.TYPE

    return $ L.TyForAll (L.NamedTyBndr a) 
                    (L.TyFun
                        integral'
                        (L.TyFun
                            tva
                            integerT
                        )
                    )


lhFromRationalM :: LHStateM L.Id
lhFromRationalM = do
    n <- liftTCValues lhFromRational
    return . L.Id n =<< fractionalT

fractionalT :: LHStateM L.Type
fractionalT = do
    a <- freshIdN L.TYPE
    let tva = L.TyVar a
    fractional <- return . KV.fractionalTC =<< knownValues
    rationalT <- tyRationalT

    let fractional' = L.TyCon fractional L.TYPE

    return $ L.TyForAll (L.NamedTyBndr a) 
                    (L.TyFun
                        fractional'
                        (L.TyFun
                            rationalT
                            tva
                        )
                    )

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

lhOrdM :: LHStateM L.Name
lhOrdM = liftTCValues lhOrd

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
