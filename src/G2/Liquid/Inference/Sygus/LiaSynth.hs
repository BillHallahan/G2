{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.Sygus.LiaSynth ( SynthRes (..)
                                          , Size
                                          , ModelNames (..)
                                          , liaSynth

                                          , MaxSize
                                          , initMaxSize
                                          , incrMaxSize) where

import G2.Language as G2
import qualified G2.Language.ExprEnv as E
import G2.Liquid.Conversion
import G2.Liquid.Helpers
import G2.Liquid.Interface
import G2.Liquid.Types
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.FuncConstraint
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.GeneratedSpecs
import G2.Liquid.Inference.PolyRef

import G2.Solver as Solver

import Control.Monad.IO.Class 

import Language.Haskell.Liquid.Types as LH hiding (SP)
import Language.Haskell.Liquid.Types.RefType
import Language.Fixpoint.Types.Constraints
import Language.Fixpoint.Types.Refinements as LH
import qualified Language.Fixpoint.Types as LH
import qualified Language.Fixpoint.Types as LHF

import Data.Coerce
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid (Sum (..))
import qualified Data.Text as T
import qualified Text.Builder as TB

import Debug.Trace
import G2.Lib.Printers

data SynthRes = SynthEnv
                  GeneratedSpecs -- ^ The synthesized specifications
                  Size -- ^ The size that the synthesizer succeeded at
                  SMTModel -- ^ An SMTModel corresponding to the new specifications
              | SynthFail FuncConstraints

data Coeffs = Coeffs { c_active :: SMTName
                     , c_op_branch1 :: SMTName
                     , c_op_branch2 :: SMTName
                     , b0 :: SMTName
                     , ars_coeffs :: [SMTName]
                     , rets_coeffs :: [SMTName] }
                     deriving Show

coeffs :: Coeffs -> [SMTName]
coeffs cf = b0 cf:ars_coeffs cf ++ rets_coeffs cf

type Clause = (SMTName, [Coeffs]) 
type CNF = [Clause]

-- Internal Types
data SpecInfo = SI { s_max_coeff :: Integer
                   
                   -- A function that is used to record the value of the function at known points,
                   -- i.e. points that occur in the FuncConstraints
                   , s_known_pre :: FixedSpec
                   , s_known_post :: FixedSpec

                   -- A function specification that must be synthesized in the future, at a lower level
                   , s_to_be_pre :: ToBeSpec 
                   , s_to_be_post :: ToBeSpec 

                   -- Functions that capture the pre and post condition.
                   -- We have one precondition function per argument
                   , s_syn_pre :: [PolyBound SynthSpec]
                   , s_syn_post :: PolyBound SynthSpec

                   , s_status :: Status }
                   deriving (Show)

s_known_pre_name :: SpecInfo -> SMTName
s_known_pre_name = fs_name . s_known_pre

s_known_pre_args :: SpecInfo -> [SpecArg]
s_known_pre_args = fs_args . s_known_pre

s_known_post_name :: SpecInfo -> SMTName
s_known_post_name = fs_name . s_known_post

s_known_post_args :: SpecInfo -> [SpecArg]
s_known_post_args = fs_args . s_known_post

s_to_be_pre_name :: SpecInfo -> SMTName
s_to_be_pre_name = tb_name . s_to_be_pre

s_to_be_post_name :: SpecInfo -> SMTName
s_to_be_post_name = tb_name . s_to_be_post

data FixedSpec = FixedSpec { fs_name :: SMTName
                           , fs_args :: [SpecArg] }
                           deriving (Show)

data ToBeSpec = ToBeSpec { tb_name :: SMTName
                         , tb_args :: [SpecArg] }
                         deriving (Show)

data SynthSpec = SynthSpec { sy_name :: SMTName
                           , sy_args :: [SpecArg]
                           , sy_rets :: [SpecArg]
                           , sy_coeffs :: CNF }
                           deriving (Show)

sy_args_and_ret :: SynthSpec -> [SpecArg]
sy_args_and_ret si = sy_args si ++ sy_rets si

data SpecArg = SpecArg { lh_rep :: LH.Expr
                       , smt_var :: SMTName
                       , smt_sort :: Sort}
                       deriving (Show)

data Status = Synth -- ^ A specification should be synthesized
            | ToBeSynthed -- ^ The specification will be synthesized at some lower level
            | Known -- ^ The specification is completely fixed
            deriving (Eq, Show)

type NMExprEnv = HM.HashMap (T.Text, Maybe T.Text) G2.Expr

newtype MaxSize = MaxSize Integer
type Size = Integer

-- A list of functions that still must have specifications synthesized at a lower level
type ToBeNames = [Name]

-- A list of functions to synthesize a the current level
type ToSynthNames = [Name]

data ModelNames = MNAll | MNOnly [Name]
                  deriving (Eq, Show, Read)

initMaxSize :: MaxSize
initMaxSize = MaxSize 1

incrMaxSize :: MaxSize -> MaxSize
incrMaxSize (MaxSize sz) = MaxSize (sz + 1)

liaSynth :: (InfConfigM m, MonadIO m, SMTConverter con ast out io)
         => con -> [GhcInfo] -> LiquidReadyState -> Evals Bool -> MeasureExs
         -> MaxSize
         -> FuncConstraints
         -> HM.HashMap Size [(ModelNames, SMTModel)] -- ^ SMT Models to block being returned by the synthesizer at various sizes
         -> ToBeNames -> ToSynthNames -> m SynthRes
liaSynth con ghci lrs evals meas_ex max_sz fc mdls to_be_ns ns_synth = do
    -- Compensate for zeroed out names in FuncConstraints
    let ns = map (\(Name n m _ l) -> Name n m 0 l) ns_synth

    -- Figure out the type of each of the functions we need to synthesize
    let eenv = expr_env . state $ lr_state lrs
        eenv' = HM.fromList . map (\(n, e) -> ((nameOcc n, nameModule n), e)) $ E.toExprList eenv
        tc = type_classes . state $ lr_state lrs
        es = map (\n -> case HM.lookup (nameOcc n, nameModule n) eenv' of
                            Just e' -> e'
                            Nothing -> error $ "synthesize: No expr found") ns
        ts = map generateRelTypes es

    -- Figure out what the other functions relevant to the current spec are
    let all_calls = concatMap allCallNames $ toListFC fc
        non_ns = filter (`notElem` ns) all_calls
        non_es = map (\n -> case HM.lookup (nameOcc n, nameModule n) eenv' of
                                        Just e' -> e'
                                        Nothing -> error $ "synthesize: No expr found") non_ns
        non_ts = map generateRelTypes non_es

    -- Form tuples of:
    -- (1) Func Names
    -- (2) Function Argument Types
    -- (3) Function Known Types
    -- to be used in forming SpecInfo's
    let ns_aty_rty = zip ns ts

        other_aty_rty = zip non_ns non_ts
        to_be_ns' = map zeroOutName to_be_ns
        (to_be_ns_aty_rty, known_ns_aty_rty) = L.partition (\(n, _) -> n `elem` to_be_ns') other_aty_rty

    let si = buildSpecInfo con tc ghci lrs ns_aty_rty to_be_ns_aty_rty known_ns_aty_rty meas_ex fc

    liftIO . putStrLn $ "si = " ++ show si

    let meas = lrsMeasures ghci lrs

    synth con eenv' tc meas meas_ex evals si max_sz fc mdls 1
    where
      zeroOutName (Name n m _ l) = Name n m 0 l

buildSpecInfo :: con -> TypeClasses -> [GhcInfo] -> LiquidReadyState
              -> [(Name, ([Type], Type))] -> [(Name, ([Type], Type))] -> [(Name, ([Type], Type))]
              -> MeasureExs -> FuncConstraints -> M.Map Name SpecInfo
buildSpecInfo con tc ghci lrs ns_aty_rty to_be_ns_aty_rty known_ns_aty_rty meas_exs fc =
    let 
        meas = lrsMeasures ghci lrs

        si = foldr (\(n, (at, rt)) -> M.insert n (buildSI tc meas Synth ghci n at rt)) M.empty ns_aty_rty
        si' = foldr (\(n, (at, rt)) -> M.insert n (buildSI tc meas ToBeSynthed ghci n at rt)) si to_be_ns_aty_rty
        si'' = foldr (\(n, (at, rt)) -> M.insert n (buildSI tc meas Known ghci n at rt)) si' known_ns_aty_rty
    in
    si''

liaSynthOfSize :: Integer -> M.Map Name SpecInfo -> M.Map Name SpecInfo
liaSynthOfSize sz m_si =
    let
        m_si' =
            M.map (\si -> 
                    let
                        s_syn_pre' =
                            map (mapPB
                                    (\psi ->
                                        psi { sy_coeffs = list_i_j (sy_name psi) (length $ sy_args psi) (length $ sy_rets psi) }
                                    )
                                 ) (s_syn_pre si)
                        s_syn_post' =
                            mapPB (\psi -> 
                                        psi { sy_coeffs = list_i_j (sy_name psi) (length $ sy_args psi) (length $ sy_rets psi) }
                                  ) (s_syn_post si)
                    in
                    si { s_syn_pre = s_syn_pre' -- (s_syn_pre si) { sy_coeffs = pre_c }
                       , s_syn_post = s_syn_post' -- (s_syn_post si) { sy_coeffs = post_c }
                       , s_max_coeff = 2 * sz }) m_si
    in
    m_si'
    where
        list_i_j s ars rets =
            [ 
                (
                    s ++ "_c_act_" ++ show j
                ,
                    [ Coeffs
                        {
                          c_active = s ++ "_f_act_" ++ show j ++ "_t_" ++ show k
                        , c_op_branch1 = s ++ "_op1_" ++ show j ++ "_t_" ++ show k
                        , c_op_branch2 = s ++ "_op2_" ++ show j ++ "_t_" ++ show k
                        , b0 = s ++ "_b_" ++ show j ++ "_t_" ++ show k
                        , ars_coeffs = 
                            [ s ++ "_a_c_" ++ show j ++ "_t_" ++ show k ++ "_a_" ++ show a
                            | a <- [1..ars]]
                        , rets_coeffs = 
                            [ s ++ "_r_c_" ++ show j ++ "_t_" ++ show k ++ "_a_" ++ show a
                            | a <- [1..rets]]
                        }
                    | k <- [1] {- [1..sz] -} ] -- Ors
                )
            | j <-  [1..sz] ] -- Ands

synth :: (InfConfigM m, MonadIO m, SMTConverter con ast out io)
      => con
      -> NMExprEnv
      -> TypeClasses
      -> Measures
      -> MeasureExs
      -> Evals Bool
      -> M.Map Name SpecInfo
      -> MaxSize
      -> FuncConstraints
      -> HM.HashMap Size [(ModelNames, SMTModel)]
      -> Size
      -> m SynthRes
synth con eenv tc meas meas_ex evals si ms@(MaxSize max_sz) fc mdls sz = do
    let si' = liaSynthOfSize sz si
        zero_coeff_hdrs = softCoeffAssertZero si' -- ++ softFuncActAssertZero si' ++ softClauseActAssertZero si'
        -- zero_coeff_hdrs = softFuncActAssertZero si' ++ softClauseActAssertZero si'
        -- zero_coeff_hdrs = softCoeffAssertZero si' -- softFuncActAssertZero si' ++ softClauseActAssertZero si'
        max_coeffs_cons = maxCoeffConstraints si'
        
        rel_mdls = map (uncurry (filterModelToRel si')) $ HM.lookupDefault [] sz mdls
        block_mdls = map blockModelDirectly rel_mdls
        fun_block_mdls = concatMap (uncurry (blockModelWithFuns si')) $ zip (map show [0..]) rel_mdls

        ex_assrts =    [Comment "favor making coefficients 0"]
                    ++ zero_coeff_hdrs
                    ++ [Comment "enforce maximal and minimal values for coefficients"]
                    ++ max_coeffs_cons
                    ++ [Comment "block spurious models"]
                    ++ block_mdls
                    ++ fun_block_mdls

    res <- synth' con eenv tc meas meas_ex evals si' fc ex_assrts sz
    case res of
        SynthEnv _ _ _ -> return res
        SynthFail _
          | sz < max_sz -> synth con eenv tc meas meas_ex evals si ms fc mdls (sz + 1)
          | otherwise -> return res
    
synth' :: (InfConfigM m, MonadIO m, SMTConverter con ast out io)
       => con
       -> NMExprEnv
       -> TypeClasses
       -> Measures
       -> MeasureExs
       -> Evals Bool
       -> M.Map Name SpecInfo
       -> FuncConstraints
       -> [SMTHeader]
       -> Size
       -> m SynthRes
synth' con eenv tc meas meas_ex evals m_si fc headers sz = do
    let n_for_m = namesForModel m_si
    liftIO $ print m_si
    let (cons, nm_fc_map) = nonMaxCoeffConstraints eenv tc meas meas_ex evals m_si fc
        hdrs = cons ++ headers

    mdl <- liftIO $ constraintsToModelOrUnsatCore con hdrs n_for_m

    case mdl of
        Right mdl' -> do
            let gs' = modelToGS m_si mdl'
            liftIO $ print gs'
            return (SynthEnv gs' sz mdl')
        Left uc ->
            let
                fc_uc = fromSingletonFC . NotFC . AndFC . map (nm_fc_map HM.!) $ HS.toList uc
            in
            return (SynthFail fc_uc)

------------------------------------
-- Handling Models
------------------------------------

namesForModel :: M.Map Name SpecInfo -> [(SMTName, Sort)]
namesForModel = concat . map siNamesForModel . M.elems

siNamesForModel :: SpecInfo -> [(SMTName, Sort)]
siNamesForModel si =
    let
        all_coeffs = zip (siGetCoeffs si) (repeat SortInt)
        all_acts = zip (siGetActs si) (repeat SortInt)
        all_op_branch = zip (siGetOpBranches si) (repeat SortBool)
    in
    all_coeffs ++ all_acts ++ all_op_branch

modelToGS :: M.Map Name SpecInfo -> SMTModel -> GeneratedSpecs
modelToGS m_si mdl =
  let
      lh_spec = M.map (\si -> buildLIA_LH si mdl) . M.filter (\si -> s_status si == Synth) $ m_si
  in
  M.foldrWithKey insertAssertGS emptyGS lh_spec

-- | Generates an Assert that, when added to a formula with the relevant variables,
-- blocks it from returning the model
blockModelDirectly :: SMTModel -> SMTHeader
blockModelDirectly = Solver.Assert . (:!) . foldr (.&&.) (VBool True) . map (\(n, v) -> V n (sortOf v) := v) . M.toList

-- | Filters a model to only those variable bindings relevant to the functions listed in the name bindings
filterModelToRel :: M.Map Name SpecInfo -> ModelNames -> SMTModel -> SMTModel
filterModelToRel m_si ns mdl =
    let
        si = case ns of
                MNOnly ns' -> mapMaybe (flip M.lookup m_si) ns'
                MNAll  -> M.elems m_si
        vs = map fst $ concatMap siNamesForModel si
    in
      flip (foldr filterClauseActiveBooleans) si
    . flip (foldr filterCoeffActiveBooleans) si
    . flip (foldr filterRelOpBranch) si
    $ M.filterWithKey (\n _ -> n `elem` vs) mdl

-- If the clause level boolean is set to true, we remove all the
-- formula level active booleans, since the formulas are
-- irrelevant.
filterClauseActiveBooleans :: SpecInfo -> SMTModel -> SMTModel
filterClauseActiveBooleans si mdl =
    let
        clauses = allCNFs si
    in
    foldr (\(cl_act, cfs) mdl_ -> if
              | M.lookup cl_act mdl_ == Just (VBool True) ->
                  foldr (\c -> M.delete (c_active c)) mdl_ cfs
              | otherwise -> mdl_) mdl clauses

-- If the formula level active booleans are set to false, we remove all the
-- coefficients in the formula, since the formula is now irrelevant.
filterCoeffActiveBooleans :: SpecInfo -> SMTModel -> SMTModel
filterCoeffActiveBooleans si mdl =
    let
        clauses = allCNFs si
        cffs = concatMap snd clauses
    in
    foldr (\cf mdl_ -> if
              | M.lookup (c_active cf) mdl_ == Just (VBool False) ->
                foldr M.delete mdl_ (coeffs cf)
              | otherwise -> mdl_) mdl cffs


filterRelOpBranch :: SpecInfo -> SMTModel -> SMTModel
filterRelOpBranch si mdl =
    let
        clauses = allCNFs si
        coeffs = concatMap snd clauses
    in
    -- If we are not using a clause, we don't care about c_op_branch1 and c_op_branch2
    -- If we are using a clause but c_op_branch1 is true, we don't care about c_op_branch2
    foldr (\(Coeffs c_act op_br1 op_br2 _ _ _) mdl_ -> if
              | M.lookup c_act mdl == Just (VBool False) ->
                  M.delete op_br2 $ M.delete op_br1 mdl_
              | M.lookup op_br1 mdl == Just (VBool True) ->
                  M.delete op_br2 mdl_
              | otherwise -> mdl) mdl coeffs

blockModelWithFuns :: M.Map Name SpecInfo -> String -> SMTModel -> [SMTHeader]
blockModelWithFuns si s mdl =
    let
        e_si = M.elems $ M.filter (\si' -> s_status si' == Synth) si

        vars = map (uncurry blockVars) $ zip (map (\i -> s ++ "_" ++ show i) [0..]) e_si

        var_defs = map (flip VarDecl SortInt . TB.text . T.pack)
                 . concat
                 . concatMap extractValues
                 . (\(x, y) -> concat x ++ y)
                 $ unzip vars

        si_nsi =   map (\(i, si') -> (si', renameByAdding i si'))
                 . zip (map (\i -> s ++ "_" ++ show i) [0..])
                 $ e_si

        fun_defs = concatMap (defineModelLIAFuns mdl . snd) si_nsi

        eqs = map (\(vs, (si', nsi')) -> mkEqualityAST vs si' nsi') $ zip vars si_nsi

        neq = [Solver.Assert . (:!) $ mkSMTAnd eqs]
    
    in
    var_defs ++ fun_defs ++ neq


-- Building function defintions
defineModelLIAFuns :: SMTModel -> SpecInfo -> [SMTHeader]
defineModelLIAFuns mdl si =
    if s_status si == Synth
        then 
               map (defineModelLIAFuncSF mdl) (extractValues $ s_syn_post si)
            ++ map (defineModelLIAFuncSF mdl) (concatMap extractValues $ s_syn_pre si)
        else []

defineModelLIAFuncSF :: SMTModel -> SynthSpec -> SMTHeader
defineModelLIAFuncSF mdl sf = 
    let
        ars_nm = map smt_var (sy_args_and_ret sf)
        ars = zip ars_nm (repeat SortInt)
    in
    DefineFun (sy_name sf) ars SortBool (buildLIA_SMT_fromModel mdl (sy_coeffs sf) ars_nm)

renameByAdding :: String -> SpecInfo -> SpecInfo
renameByAdding i si =
    si { s_syn_pre = map (mapPB rn) $ s_syn_pre si
       , s_syn_post = mapPB rn $ s_syn_post si
       }
    where
        rn s = s { sy_name = sy_name s ++ "_MDL_" ++ i }

buildLIA_SMT_fromModel :: SMTModel -> [(SMTName, [Coeffs])] -> [SMTName] -> SMTAST
buildLIA_SMT_fromModel mdl = buildLIA (:+) (:*) (:=) (:>) (:>=) Ite mkSMTAnd mkSMTAnd mkSMTOr vint VInt vbool
    where
        vint n
            | Just v <- M.lookup n mdl = v
            | otherwise = VInt 0

        vbool n
            | Just v <- M.lookup n mdl = v
            | otherwise = VBool False


blockVars :: String -> SpecInfo -> ([PolyBound [SMTName]], PolyBound [SMTName])
blockVars str si = ( map (uncurry mk_blk_vars) . zip (map show [0..]) $ s_syn_pre si
                   , mk_blk_vars "r" $ s_syn_post si)
    where
        mk_blk_vars i sy_s = mapPB (\(j, s) -> 
                                          map (\k -> "x_MDL_" ++ str ++ "_" ++ i ++ "_" ++ show j ++ "_" ++ show k)
                                        . map fst
                                        . zip [0..]
                                        $ sy_args_and_ret s
                                 )
                         $ zipPB (uniqueIds sy_s) sy_s

mkEqualityAST :: ([PolyBound [SMTName]], PolyBound [SMTName]) -> SpecInfo -> SpecInfo -> SMTAST
mkEqualityAST (avs, rvs) si nsi =
    let
        pre_eq =
            map (\(vs, s_sp, ns_sp) -> 
                        mapPB 
                          (\(vs', s_sp', ns_sp') -> 
                                  let
                                      smt_vs = map (flip V SortInt) vs'
                                  in
                                  Func (sy_name s_sp') smt_vs :/= Func (sy_name ns_sp') smt_vs
                          ) $ zip3PB vs s_sp ns_sp
                )
            $ zip3 avs (s_syn_pre si) (s_syn_pre nsi)

        pre_eq' = concatMap extractValues pre_eq

        post_eq =
            mapPB 
                (\(vs, s_sp, ns_sp) -> 
                        let
                            smt_vs = map (flip V SortInt) vs
                        in
                        Func (sy_name s_sp) smt_vs :/= Func (sy_name ns_sp) smt_vs
                ) $ zip3PB rvs (s_syn_post si) (s_syn_post nsi)

        post_eq' = extractValues post_eq
    in
    mkSMTAnd (post_eq' ++ pre_eq')

------------------------------------
-- Building SMT Formulas
------------------------------------

mkPreCall :: NMExprEnv -> TypeClasses -> Measures -> MeasureExs -> Evals (Integer, Bool) -> M.Map Name SpecInfo -> FuncCall -> SMTAST
mkPreCall eenv tc meas meas_ex evals m_si fc@(FuncCall { funcName = n, arguments = ars })
    | Just si <- M.lookup n m_si
    , Just (ev_i, _) <- lookupEvals fc (pre_evals evals)
    , Just func_e <- HM.lookup (nameOcc n, nameModule n) eenv =
        let
            func_ts = argumentTypes func_e

            v_ars = filter (validArgForSMT . snd)
                  . filter (\(t, _) -> not (isTyFun t) && not (isTyVar t))
                  $ zip func_ts ars

            sy_body_p =
                concatMap
                    (\(si_pb, ts_es) ->
                        let
                            t_ars = init ts_es
                            smt_ars = concatMap (map exprToSMT) $ map (uncurry (adjustArgs meas meas_ex)) t_ars

                            (l_rt, l_re) = last ts_es
                            re_pb = extractExprPolyBoundWithRoot l_re
                            rt_pb = extractTypePolyBound l_rt


                            re_rt_pb = filterPBByType snd $ zipPB re_pb rt_pb
                            si_re_rt_pb = case re_rt_pb of
                                              Just re_rt_pb -> zipWithPB (\x (y, z) -> (x, y, z)) si_pb re_rt_pb
                                              Nothing -> error "mkPreCall: impossible, the polybound should have already been filtered"
                        in
                        concatMap
                            (\(psi, re, rt) ->
                                let
                                    smt_r = map (map exprToSMT) $ map (adjustArgs meas meas_ex rt) re
                                in
                                map (\r -> Func (sy_name psi) $ smt_ars ++ r) smt_r
                              ) $ extractValues si_re_rt_pb
                  ) . zip (s_syn_pre si) . filter (not . null) $ L.inits v_ars

            sy_body = foldr (.&&.) (VBool True) sy_body_p
            fixed_body = Func (s_known_pre_name si) [VInt ev_i]
            to_be_body = Func (s_to_be_pre_name si) [VInt ev_i]
        in
        case s_status si of
                Synth -> fixed_body :&& sy_body
                ToBeSynthed -> fixed_body :&& to_be_body
                Known -> fixed_body
    | otherwise = error "mkPreCall: specification not found"

mkPostCall :: NMExprEnv -> TypeClasses -> Measures -> MeasureExs -> Evals (Integer, Bool) -> M.Map Name SpecInfo -> FuncCall -> SMTAST
mkPostCall eenv tc meas meas_ex evals m_si fc@(FuncCall { funcName = n, arguments = ars, returns = r })
    | Just si <- M.lookup n m_si
    , Just (ev_i, _) <- lookupEvals fc (post_evals evals)
    , Just func_e <- HM.lookup (nameOcc n, nameModule n) eenv =
        let
            func_ts = argumentTypes func_e

            smt_ars = map exprToSMT
                    . concatMap (uncurry (adjustArgs meas meas_ex))
                    . filter (\(t, _) -> not (isTyFun t) && not (isTyVar t))
                    . filter (validArgForSMT . snd) $ zip func_ts ars
            
            smt_ret = extractExprPolyBoundWithRoot r
            smt_ret_ty = extractTypePolyBound (returnType func_e)
            smt_ret_e_ty = case filterPBByType snd $ zipPB smt_ret smt_ret_ty of
                              Just smt_ret_e_ty' -> smt_ret_e_ty'
                              Nothing -> PolyBound ([], headValue smt_ret_ty) []

            sy_body = foldr (.&&.) (VBool True)
                    . concatMap
                        (\(syn_p, r, rt) ->
                            let
                                adj_r = map (adjustArgs meas meas_ex rt) $ r
                                smt_r = map (map exprToSMT) adj_r
                            in
                            map (\smt_r' -> Func (sy_name syn_p) $ smt_ars ++ smt_r') smt_r)
                    . extractValues 
                    $ zipWithPB (\x (y, z) -> (x, y, z)) (s_syn_post si) smt_ret_e_ty
            fixed_body = Func (s_known_post_name si) [VInt ev_i]
            to_be_body = Func (s_to_be_post_name si) [VInt ev_i]
        in
        case s_status si of
                Synth -> fixed_body :&& sy_body
                ToBeSynthed -> fixed_body :&& to_be_body
                Known -> fixed_body
    | otherwise = error "mkPostCall: specification not found"

constraintsToSMT :: NMExprEnv -> TypeClasses -> Measures -> MeasureExs -> Evals (Integer, Bool)  -> M.Map Name SpecInfo -> FuncConstraints -> [SMTHeader]
constraintsToSMT eenv tc meas meas_ex evals si =
    map Solver.Assert . map (constraintToSMT eenv tc meas meas_ex evals si) . toListFC

constraintToSMT :: NMExprEnv -> TypeClasses -> Measures -> MeasureExs -> Evals (Integer, Bool)  -> M.Map Name SpecInfo -> FuncConstraint -> SMTAST
constraintToSMT eenv tc meas meas_ex evals si (Call All fc) =
    case M.lookup (funcName fc) si of
        Just si' ->
            let
                pre = mkPreCall eenv tc meas meas_ex evals si fc
                post = mkPostCall eenv tc meas meas_ex evals si fc
            in
            pre :=> post
        Nothing -> error "constraintToSMT: specification not found"
constraintToSMT eenv tc meas meas_ex evals si (Call Pre fc) =
    case M.lookup (funcName fc) si of
        Just si' ->
            mkPreCall eenv tc meas meas_ex evals si fc
        Nothing -> error $ "constraintToSMT: specification not found" ++ show fc
constraintToSMT eenv tc meas meas_ex evals si (Call Post fc) =
    case M.lookup (funcName fc) si of
        Just si' -> mkPostCall eenv tc meas meas_ex evals si fc
        Nothing -> error "constraintToSMT: specification not found"
constraintToSMT eenv tc meas meas_ex evals si (AndFC fs) = mkSMTAnd $ map (constraintToSMT eenv tc meas meas_ex evals si) fs
constraintToSMT eenv tc meas meas_ex evals si (OrFC fs) = mkSMTOr $ map (constraintToSMT eenv tc meas meas_ex evals si) fs
constraintToSMT eenv tc meas meas_ex evals si (ImpliesFC fc1 fc2) =
    constraintToSMT eenv tc meas meas_ex evals si fc1 :=> constraintToSMT eenv tc meas meas_ex evals si fc2
constraintToSMT eenv tc meas meas_ex evals si (NotFC fc) = (:!) (constraintToSMT eenv tc meas meas_ex evals si fc)

adjustArgs :: Measures -> MeasureExs -> Type -> G2.Expr -> [G2.Expr]
adjustArgs meas meas_ex t = map adjustLits . substMeasures meas meas_ex t

substMeasures :: Measures -> MeasureExs -> Type -> G2.Expr -> [G2.Expr]
substMeasures meas meas_ex t e =
    case typeToSort t of
        Just _ -> [e]
        Nothing ->
            case HM.lookup e meas_ex of
                Just es ->
                    let
                        -- Get a list of all measure/output pairs with usable types
                        es' = filter (isJust . typeToSort . returnType
                                     . fromJust . flip E.lookup meas . fst)
                            . filter (isJust . typeToSort . returnType . snd) $ HM.toList es
                        -- Make sure that es's type is specific enough to be used with the measure
                        app_meas = applicableMeasures meas t
                        es'' = filter (\(n, _) -> n `E.member` app_meas) es'
                    in
                    -- Sort to make sure we get the same order consistently
                    map snd $ L.sortBy (\(n1, _) (n2, _) -> compare n1 n2) es''
                Nothing -> []

adjustLits :: G2.Expr -> G2.Expr
adjustLits (App _ l@(Lit _)) = l
adjustLits e = e

validArgForSMT :: G2.Expr -> Bool
validArgForSMT e = not (isLHDict e) && not (isType e)
    where
        isType (Type _) = True
        isType _ = False

        isLHDict e
            | (TyCon (Name n _ _ _) _):_ <- unTyApp (typeOf e) = n == "lh"
            | otherwise = False


-- computing F_{Fixed}, i.e. what is the value of known specifications at known points 
envToSMT :: MeasureExs -> Evals (Integer, Bool)  -> M.Map Name SpecInfo -> FuncConstraints
         -> ([SMTHeader], HM.HashMap SMTName FuncConstraint)
envToSMT meas_ex evals si fc =
    let
        nm_fc = zip ["f" ++ show i | i <- [1..]]
              . L.nub
              $ allCallsFC fc

        calls = concatMap (uncurry (flip (envToSMT' meas_ex evals si))) nm_fc

        known_id_calls = map fst calls
        real_calls = map snd calls

        assrts = map Solver.Assert known_id_calls
               
    in
    (assrts, HM.fromList real_calls)

envToSMT' :: MeasureExs -> Evals (Integer, Bool)  -> M.Map Name SpecInfo -> FuncCall -> SMTName -> [(SMTAST, (SMTName, FuncConstraint))]
envToSMT' meas_ex (Evals {pre_evals = pre_ev, post_evals = post_ev}) m_si fc@(FuncCall { funcName = f }) uc_n =
    case M.lookup f m_si of
        Just si ->
            let
                (pre_i, pre_res) = case lookupEvals fc pre_ev of
                                        Just b -> b
                                        Nothing -> error "envToSMT': pre not found"

                (post_i, post_res) = case lookupEvals fc post_ev of
                                        Just b -> b
                                        Nothing -> error "envToSMT': post not found"

                (pre_op, pre_op_fc) = if pre_res then (id, id) else ((:!), NotFC)
                (post_op, post_op_fc) = if post_res then (id, id) else ((:!), NotFC)

                pre = pre_op $ Func (s_known_pre_name si) [VInt pre_i]
                post = post_op $ Func (s_known_post_name si) [VInt post_i]

                pre_real = pre_op_fc (Call Pre fc)
                post_real = post_op_fc (Call Post fc)

                pre_name = "pre_" ++ uc_n
                post_name = "post_" ++ uc_n
            in
            [ (Named pre pre_name, (pre_name, pre_real))
            , (Named post post_name, (post_name, post_real))]
        Nothing -> error "envToSMT': function not found"

mkRetNonZero :: M.Map Name SpecInfo -> [SMTHeader]
mkRetNonZero = concatMap mkRetNonZero' . filter (\si -> s_status si == Synth) . M.elems

mkRetNonZero' :: SpecInfo -> [SMTHeader]
mkRetNonZero' si =
    let
        sy_sps = allSynthSpec si
    in
    concatMap (\sys ->
              let
                  cffs = sy_coeffs sys
              in
              map
                  (\(act, cff) ->
                          Solver.Assert (((:!) $ V act SortBool) :=> mkSMTOr (map (\c -> mkCoeffRetNonZero c) cff))
                  ) cffs
              ) sy_sps

mkCoeffRetNonZero :: Coeffs -> SMTAST
mkCoeffRetNonZero cffs =
    let
        act = c_active cffs
        ret_cffs = rets_coeffs cffs
    in
    case null ret_cffs of
        True -> VBool True
        False -> 
            V act SortBool :=> mkSMTOr (map (\r -> V r SortInt :/= VInt 0) ret_cffs)

-- This function aims to limit the number of different models that can be produced
-- that result in equivalent specifications. 
-- This is important, because as a fallback when counterexamples are not
-- blocking bad solutions, we instead negate SMT models.  So we want as
-- few different, but ultimately equivalent, models as possible.
-- In particualar:
-- (1) If the formula level active booleans are set to false, we force all the
-- coefficients in the formula to be 0, since the formula is now irrelevant.
-- (2) Similarly, if the clause level boolean is set to true, we force all the
-- formula level active booleans to be false, since the formulas are
-- irrelevant.
limitEquivModels :: M.Map Name SpecInfo -> [SMTHeader]
limitEquivModels m_si =
    let
        a_si = filter (\si -> s_status si == Synth) $ M.elems m_si
        -- (1)
        clauses = concatMap allCNFs a_si
        cl_imp_coeff = concatMap
                          (\(cl_act, cffs) ->
                            map (\cf -> V cl_act SortBool :=> ((:!) $ V (c_active cf) SortBool)) cffs
                          ) clauses 

        -- (2)
        cffs = concatMap snd clauses
        coeff_act_imp_zero = concatMap
                                 (\cf ->
                                      map (\c -> ((:!) $ V (c_active cf) SortBool) :=> (V c SortInt := VInt 0)) (coeffs cf)
                                 ) cffs
    in
    map Solver.Assert $ cl_imp_coeff ++ coeff_act_imp_zero

softCoeffAssertZero :: M.Map Name SpecInfo -> [SMTHeader]
softCoeffAssertZero = map (\n -> AssertSoft (V n SortInt := VInt 0)) . getCoeffs

softFuncActAssertZero :: M.Map Name SpecInfo -> [SMTHeader]
softFuncActAssertZero = map (\n -> AssertSoft ((:!) $ V n SortBool)) . getFuncActs

softClauseActAssertZero :: M.Map Name SpecInfo -> [SMTHeader]
softClauseActAssertZero = map (\n -> AssertSoft (V n SortBool)) . getClauseActs

maxCoeffConstraints :: M.Map Name SpecInfo -> [SMTHeader]
maxCoeffConstraints =
      map Solver.Assert
    . concatMap
        (\si ->
            let
                cffs = concatMap coeffs . concatMap snd $ allPreCoeffs si ++ allPostCoeffs si
            in
            if s_status si == Synth
                then map (\c -> (Neg (VInt (s_max_coeff si)) :<= V c SortInt)
                                    :&& (V c SortInt :<= VInt (s_max_coeff si))) cffs
                else []) . M.elems

nonMaxCoeffConstraints :: NMExprEnv -> TypeClasses -> Measures -> MeasureExs -> Evals Bool  -> M.Map Name SpecInfo -> FuncConstraints
                       -> ([SMTHeader], HM.HashMap SMTName FuncConstraint)
nonMaxCoeffConstraints eenv tc meas meas_ex evals m_si fc =
    let
        evals' = assignIds evals
        
        all_acts = getActs m_si
        all_coeffs = getCoeffs m_si
        get_ops = getOpBranches m_si

        var_act_hdrs = map (flip VarDecl SortBool . TB.text . T.pack) all_acts
        var_int_hdrs = map (flip VarDecl SortInt . TB.text . T.pack) all_coeffs
        var_op_hdrs = map (flip VarDecl SortBool . TB.text . T.pack) get_ops

        def_funs = concatMap defineLIAFuns $ M.elems m_si
        fc_smt = constraintsToSMT eenv tc meas meas_ex evals' m_si fc
        (env_smt, nm_fc) = envToSMT meas_ex evals' m_si fc

        ret_is_non_zero = mkRetNonZero m_si

        lim_equiv_smt = limitEquivModels m_si
    in
    (    var_act_hdrs
      ++ var_int_hdrs
      ++ var_op_hdrs
      ++ def_funs
      ++ [Comment "encode specification constraints"]
      ++ fc_smt
      ++ [Comment "encode the environment"]
      ++ env_smt 
      ++ [Comment "force return values to be nonzero"]
      ++ ret_is_non_zero 
      ++ [Comment "block equivalent formulas"]
      ++ lim_equiv_smt
    , nm_fc)


getCoeffs :: M.Map Name SpecInfo -> [SMTName]
getCoeffs = concatMap siGetCoeffs . M.elems

siGetCoeffs :: SpecInfo -> [SMTName]
siGetCoeffs si
    | s_status si == Synth = concatMap coeffs . concatMap snd $ allCNFs si
    | otherwise = []

getOpBranches:: M.Map Name SpecInfo -> [SMTName]
getOpBranches = concatMap siGetOpBranches . M.elems

siGetOpBranches :: SpecInfo -> [SMTName]
siGetOpBranches si
    | s_status si == Synth =
        concatMap (\c -> [c_op_branch1 c, c_op_branch2 c]) . concatMap snd $ allCNFs si
    | otherwise = []

getActs :: M.Map Name SpecInfo -> [SMTName]
getActs si = getClauseActs si ++ getFuncActs si

siGetActs :: SpecInfo -> [SMTName]
siGetActs si = siGetClauseActs si ++ siGetFuncActs si

getClauseActs :: M.Map Name SpecInfo -> [SMTName]
getClauseActs m_si =
    concatMap siGetClauseActs $ M.elems m_si

siGetClauseActs :: SpecInfo -> [SMTName]
siGetClauseActs si
    | s_status si == Synth = map fst $ allCNFs si
    | otherwise = []

getFuncActs :: M.Map Name SpecInfo -> [SMTName]
getFuncActs m_si =
    concatMap siGetFuncActs $ M.elems m_si

siGetFuncActs :: SpecInfo -> [SMTName]
siGetFuncActs si
    | s_status si == Synth = map c_active . concatMap snd $ allCNFs si
    | otherwise = []

-- We assign a unique id to each function call, and use these as the arguments
-- to the known functions, rather than somehow using the arguments directly.
-- This means we can get away with needing only a single known function
-- for the pre, and a single known function for the post, as opposed
-- to needing individual known functions/function calls for polymorphic refinements.
assignIds :: Evals Bool -> Evals (Integer, Bool)
assignIds = snd . mapAccumLEvals (\i b -> (i + 1, (i, b))) 0

defineLIAFuns :: SpecInfo -> [SMTHeader]
defineLIAFuns si =
    (if s_status si == Synth
        then 
               map defineSynthLIAFuncSF (extractValues $ s_syn_post si)
            ++ map defineSynthLIAFuncSF (concatMap extractValues $ s_syn_pre si)
        else [])
    ++
    [ defineFixedLIAFuncSF (s_known_pre si)
    , defineFixedLIAFuncSF (s_known_post si)
    , defineToBeFuncSF (s_to_be_pre si)
    , defineToBeFuncSF (s_to_be_post si)]

defineFixedLIAFuncSF :: FixedSpec -> SMTHeader
defineFixedLIAFuncSF fs =
    DeclareFun (fs_name fs) [SortInt] SortBool

defineToBeFuncSF :: ToBeSpec -> SMTHeader
defineToBeFuncSF tb =
    DeclareFun (tb_name tb) [SortInt] SortBool

defineSynthLIAFuncSF :: SynthSpec -> SMTHeader
defineSynthLIAFuncSF sf = 
    let
        ars_nm = map smt_var (sy_args_and_ret sf)
        ars = zip ars_nm (repeat SortInt)
    in
    DefineFun (sy_name sf) ars SortBool (buildLIA_SMT (sy_coeffs sf) ars_nm)

declareSynthLIAFuncSF :: SynthSpec -> SMTHeader
declareSynthLIAFuncSF sf =
    let
        ars = map (const SortInt) (sy_args_and_ret sf)
    in
    DeclareFun (sy_name sf) (ars) SortBool

------------------------------------
-- Building LIA Formulas
------------------------------------

type Plus a = a ->  a -> a
type Mult a = a ->  a -> a
type EqF a b = a -> a -> b
type Gt a b = a -> a -> b
type GEq a b = a -> a -> b
type Ite b a = b -> a -> a -> a
type And b c = [b] -> c
type Or b = [b] -> b
type VInt a = SMTName -> a
type CInt a = Integer -> a
type VBool b = SMTName -> b

buildLIA_SMT :: [(SMTName, [Coeffs])] -> [SMTName] -> SMTAST
buildLIA_SMT = buildLIA (:+) (:*) (:=) (:>) (:>=) Ite mkSMTAnd mkSMTAnd mkSMTOr (flip V SortInt) VInt (flip V SortBool)

-- Get a list of all LIA formulas.  We raise these as high in a PolyBound as possible,
-- because checking leaves is more expensive.  Also, checking leaves only happens if those
-- leaves exists, i.e. consider a refinement on the elements of a list [{x:a | p x}],
-- p is only checked in the nonempty case.
buildLIA_LH :: SpecInfo -> SMTModel -> [PolyBound LHF.Expr]
buildLIA_LH si mv = map (mapPB pAnd) {- . map (uncurry raiseSpecs) . zip synth_specs -} $  buildLIA_LH' si mv
    where
        synth_specs = s_syn_pre si ++ [s_syn_post si]

        pAnd xs =
            case any (== PFalse) xs of
                True -> PFalse
                False -> PAnd $ filter (/= PTrue) xs

buildLIA_LH' :: SpecInfo -> SMTModel -> [PolyBound [LH.Expr]]
buildLIA_LH' si mv =
    let
        build ars = buildLIA ePlus eTimes bEq bGt bGeq eIte id pAnd pOr (detVar ars) (ECon . I) (detBool ars)
        pre = map (mapPB (\psi -> build (sy_args_and_ret psi) (sy_coeffs psi) (map smt_var (sy_args_and_ret psi)))) $ s_syn_pre si
        post = mapPB (\psi -> build post_ars (sy_coeffs psi) (map smt_var (sy_args_and_ret psi))) $ s_syn_post si
    in
    pre ++ [post]
    where
        detVar ars v 
            | Just (VInt c) <- M.lookup v mv = ECon (I c)
            | Just sa <- L.find (\sa_ -> v == smt_var sa_) ars = lh_rep sa
            | otherwise = error "detVar: variable not found"

        detBool ars v
            | Just (VBool b) <- M.lookup v mv = if b then PTrue else PFalse
            | otherwise = error "detBool: variable not found"

        eTimes (ECon (I 0)) _ = ECon (I 0)
        eTimes _ (ECon (I 0)) = ECon (I 0)
        eTimes (ECon (I 1)) x = x
        eTimes x (ECon (I 1)) = x
        eTimes (ECon (I (-1))) x = ENeg x
        eTimes x (ECon (I (-1))) = ENeg x
        eTimes x y = EBin LH.Times x y

        ePlus (ECon (I 0)) x = x
        ePlus x (ECon (I 0)) = x
        ePlus x y = EBin LH.Plus x y

        eIte PTrue x _ = x
        eIte PFalse _ y = y
        eIte b x y = error "eIte: Should never have non-concrete bool"

        pAnd xs =
            case any (== PFalse) xs of
                True -> PFalse
                False -> PAnd $ filter (/= PTrue) xs

        pOr xs =
            case any (== PTrue) xs of
                True -> PTrue
                False -> POr $ filter (/= PFalse) xs

        bEq (ECon (I x)) (ECon (I y)) =
            if x == y then PTrue else PFalse
        bEq x y
            | x == y = PTrue
            | otherwise = PAtom LH.Eq x y

        bGt (ECon (I x)) (ECon (I y)) =
            if x > y then PTrue else PFalse
        bGt x y
            | x == y = PFalse
            | otherwise = PAtom LH.Gt x y

        bGeq (ECon (I x)) (ECon (I y)) =
            if x >= y then PTrue else PFalse
        bGeq x y
            | x == y = PTrue
            | otherwise = PAtom LH.Ge x y

        post_ars = allPostSpecArgs si

raiseSpecs :: PolyBound SynthSpec -> PolyBound [LH.Expr] -> PolyBound [LH.Expr]
raiseSpecs sy_sp pb =
    let
        symb_pb = mapPB (HS.unions . map (argsInExpr . lh_rep) . sy_args_and_ret) sy_sp
        symb_es = filter (not . HS.null . fst) . map (\e -> (argsInExpr e, e)) . concat $ extractValues pb

        null_pb = mapPB (filter (HS.null . argsInExpr)) pb
    
        r = snd $ L.mapAccumL
                (\se spb ->
                    let
                        se' = map (\(xs, e_) -> (HS.difference xs spb, e_)) se
                        (se_here, se_cont) = L.partition (HS.null . fst) se'
                        e = map snd se_here
                    in
                    (se_cont, e))
                symb_es symb_pb
    in
    trace ("sy_name sy_sb = " ++ show (sy_name (headValue sy_sp)) ++ "\npb = " ++ show pb ++ "\nr = " ++ show r)
    zipWithPB (++) null_pb r 

argsInExpr :: LH.Expr -> HS.HashSet LH.Symbol
argsInExpr (EVar symb) = HS.singleton symb
argsInExpr (ECon _) = HS.empty
argsInExpr (EApp _ x) =
    -- The left hand side of an EApp is a measure.
    -- Since we are only looking for arguments, we do not collect it
    argsInExpr x
argsInExpr (EBin _ x y) = HS.union (argsInExpr x) (argsInExpr y)
argsInExpr (PAtom _ x y) = HS.union (argsInExpr x) (argsInExpr y)
argsInExpr (PAnd xs) = HS.unions (map argsInExpr xs)
argsInExpr (POr xs) = HS.unions (map argsInExpr xs)
argsInExpr e = error $ "argsInExpr: unhandled symbol " ++ show e


buildLIA :: Plus a
         -> Mult a
         -> EqF a b
         -> Gt a b
         -> GEq a b
         -> Ite b b 
         -> And b c
         -> And b b
         -> Or b
         -> VInt a
         -> CInt a
         -> VBool b
         -> [(SMTName, [Coeffs])]
         -> [SMTName]
         -> c
buildLIA plus mult eq gt geq ite mk_and_sp mk_and mk_or vint cint vbool all_coeffs args =
    let
        lin_ineqs = map (\(cl_act, cl) -> vbool cl_act:map toLinInEqs cl) all_coeffs
    in
    mk_and_sp . map mk_or $ lin_ineqs
    where
        toLinInEqs (Coeffs { c_active = act
                           , c_op_branch1 = op_br1
                           , c_op_branch2 = op_br2
                           , b0 = b
                           , ars_coeffs = acs
                           , rets_coeffs =  rcs }) =
            let
                sm = foldr plus (cint 0)
                   . map (uncurry mult)
                   $ zip (map vint $ acs ++ rcs) (map vint args)
            in
            mk_and [vbool act, ite (vbool op_br1)
                                  (sm `eq` vint b)
                                  (ite (vbool op_br2) (sm `gt` vint b)
                                               (sm `geq` vint b)
                                  )
                   ]

------------------------------------
-- Building SpecInfos
------------------------------------

buildSI :: TypeClasses -> Measures -> Status -> [GhcInfo] ->  Name -> [Type] -> Type -> SpecInfo
buildSI tc meas stat ghci f aty rty =
    let
        smt_f = nameToStr f
        fspec = case genSpec ghci f of
                Just spec' -> spec'
                _ -> error $ "synthesize: No spec found for " ++ show f
        (outer_ars_pb, ret_pb) = argsAndRetFromSpec tc ghci meas [] aty rty fspec
        outer_ars = map fst outer_ars_pb
        ars_pb = map snd outer_ars_pb

        ret = headValue ret_pb


        arg_ns = map (\(a, i) -> a { smt_var = "x_" ++ show i } ) $ zip (concat outer_ars) [1..]
        ret_ns = map (\(r, i) -> r { smt_var = "x_r_" ++ show i }) $ zip ret [1..]
    in
    trace ("smt_f = " ++ show smt_f ++ "\nouter_ars_pb = " ++ show outer_ars_pb ++ "\nret_pb = " ++ show ret_pb ++ "\n-----")
    SI { s_max_coeff = 0
       , s_known_pre = FixedSpec { fs_name = smt_f ++ "_known_pre"
                                 , fs_args = arg_ns }
       , s_known_post = FixedSpec { fs_name = smt_f ++ "_known_post"
                                  , fs_args = arg_ns ++ ret_ns }
       , s_to_be_pre = ToBeSpec { tb_name = smt_f ++ "_to_be_pre"
                                , tb_args = arg_ns }
       , s_to_be_post = ToBeSpec { tb_name = smt_f ++ "_to_be_post"
                                 , tb_args = arg_ns ++ ret_ns }
       , s_syn_pre = map (\(ars_pb, i) ->
                                let
                                    ars = concatMap fst (init ars_pb)
                                    r_pb = snd (last ars_pb)
                                in
                                mapPB (\(rets, j) ->
                                        SynthSpec { sy_name = smt_f ++ "_synth_pre_" ++ show i ++ "_" ++ show j
                                                  , sy_args = map (\(a, k) -> a { smt_var = "x_" ++ show k}) $ zip ars [1..]
                                                  , sy_rets = map (\(r, k) -> r { smt_var = "x_r_" ++ show k}) $ zip rets [1..]
                                                  , sy_coeffs = []}
                                      )  $ zipPB r_pb (uniqueIds r_pb)
                         ) $ zip (filter (not . null) $ L.inits outer_ars_pb) [1..]
       , s_syn_post = mkSynSpecPB (smt_f ++ "_synth_post_") arg_ns ret_pb
       , s_status = stat }

argsAndRetFromSpec :: TypeClasses -> [GhcInfo] -> Measures -> [([SpecArg], PolyBound [SpecArg])] -> [Type] -> Type -> SpecType -> ([([SpecArg], PolyBound [SpecArg])], PolyBound [SpecArg])
argsAndRetFromSpec tc ghci meas ars ts rty (RAllT { rt_ty = out }) =
    argsAndRetFromSpec tc ghci meas ars ts rty out
argsAndRetFromSpec tc ghci meas ars (t:ts) rty rfun@(RFun { rt_bind = b, rt_in = i, rt_out = out}) =
    let
        (Just out_symb, sa) = mkSpecArgPB ghci meas t rfun
    in
    case i of
        RVar {} -> argsAndRetFromSpec tc ghci meas ars ts rty out
        RFun {} -> argsAndRetFromSpec tc ghci meas ars ts rty out
        _ -> argsAndRetFromSpec tc ghci meas ((out_symb, sa):ars) ts rty out
argsAndRetFromSpec _ ghci meas ars _ rty rapp@(RApp { rt_reft = ref}) =
    let
        (_, sa) = mkSpecArgPB ghci meas rty rapp
    in
    (reverse ars, sa)
argsAndRetFromSpec _ ghci meas ars _ rty rvar@(RVar { rt_reft = ref}) =
    let
        (_, sa) = mkSpecArgPB ghci meas rty rvar
    in
    (reverse ars, sa)
argsAndRetFromSpec _ ghci meas ars [] rty st@(RFun {}) = error $ "argsAndRetFromSpec: RFun with empty type list " ++ show st
argsAndRetFromSpec _ _ _ _ _ _ st = error $ "argsAndRetFromSpec: unhandled SpecType " ++ show st

mkSpecArgPB :: [GhcInfo] -> Measures -> Type -> SpecType -> (Maybe [SpecArg], PolyBound [SpecArg])
mkSpecArgPB ghci meas t st =
    let
        t_pb = extractTypePolyBound t

        sy_pb = specTypeSymbolPB st
        in_sy_pb = mapPB inner sy_pb

        t_sy_pb = filterPBByType snd $ zipPB in_sy_pb t_pb
        t_sy_pb' = case t_sy_pb of
                    Just pb -> pb
                    Nothing -> PolyBound (inner $ headValue sy_pb, t) []

        out_symb = outer $ headValue sy_pb
        out_spec_arg = fmap (\os -> mkSpecArg ghci meas os t) out_symb
    in
    (out_spec_arg, mapPB (uncurry (mkSpecArg ghci meas)) t_sy_pb')


mkSpecArg :: [GhcInfo] -> Measures -> LH.Symbol -> Type -> [SpecArg]
mkSpecArg ghci meas symb t =
    let
        srt = typeToSort t
    in
    case srt of
        Just srt' ->
            [SpecArg { lh_rep = EVar symb
                     , smt_var = "tbd"
                     , smt_sort = srt' }]
        Nothing ->
            let
                app_meas = applicableMeasuresType meas t
                app_meas' = L.sortBy (\(n1, _) (n2, _) -> compare n1 n2) app_meas
            in
            mapMaybe
                (\(mn, mt) ->
                    fmap (\srt' ->
                            let
                                lh_mn = getLHMeasureName ghci mn
                            in
                            SpecArg { lh_rep = EApp (EVar lh_mn) (EVar symb)
                                    , smt_var = "tbd"
                                    , smt_sort = srt'}) $ typeToSort mt) app_meas'


mkSynSpecPB :: String -> [SpecArg] -> PolyBound [SpecArg] -> PolyBound SynthSpec
mkSynSpecPB smt_f arg_ns pb_sa =
    mapPB (\(ui, sa) ->
            let
                ret_ns = map (\(r, i) -> r { smt_var = "x_r_" ++ show ui ++ "_" ++ show i }) $ zip sa [1..]
            in
            SynthSpec { sy_name = smt_f ++ show ui
                      , sy_args = arg_ns
                      , sy_rets = ret_ns
                      , sy_coeffs = [] }
        )
        $ zipPB (uniqueIds pb_sa) pb_sa

filterPBByType :: (v -> Type) -> PolyBound v -> Maybe (PolyBound v)
filterPBByType f = filterPB (\(PolyBound v _) ->
                                let
                                    t = f v
                                in
                                not (isTyVar t) && not (isTyFun t))

-- ret_ns = map (\(r, i) -> r { smt_var = "x_r_" ++ show i }) $ zip ret [1..]
       -- , s_syn_post = SynthSpec { sy_name = smt_f ++ "_synth_post"
       --                          , sy_args_and_ret = arg_ns ++ ret_ns
       --                          , sy_coeffs = [] }


----------------------------------------------------------------------------
-- Manipulate SpecTypes
----------------------------------------------------------------------------

specTypeSymbol :: SpecType -> LH.Symbol
specTypeSymbol (RFun { rt_bind = b }) = b
specTypeSymbol rapp@(RApp { rt_reft = ref }) = reftSymbol $ ur_reft ref
specTypeSymbol (RVar { rt_reft = ref }) = reftSymbol $ ur_reft ref
specTypeSymbol _ = error $ "specTypeSymbol: SpecType not handled"

data SymbolPair = SP { inner :: LH.Symbol, outer :: Maybe LH.Symbol }

specTypeSymbolPB :: SpecType -> PolyBound SymbolPair
specTypeSymbolPB rfun@(RFun { rt_bind = b, rt_in = i, rt_out = out}) =
    case specTypeSymbolPB i of
        PolyBound sp ps -> PolyBound (sp { outer = Just b}) ps
specTypeSymbolPB (RApp { rt_reft = ref, rt_args = ars }) =
    PolyBound (SP { inner = reftSymbol $ ur_reft ref, outer = Nothing}) $ map specTypeSymbolPB ars
specTypeSymbolPB (RVar {rt_reft = ref}) =
    PolyBound (SP { inner = reftSymbol $ ur_reft ref, outer = Nothing }) []
specTypeSymbolPB r = error $ "specTypePB: Unexpected SpecType" ++ "\n" ++ show r


specTypePB :: SpecType -> PolyBound SpecType
specTypePB rfun@(RFun { rt_bind = b, rt_in = i, rt_out = out}) = specTypePB i
specTypePB rapp@(RApp { rt_reft = ref, rt_args = ars }) =
    PolyBound rapp $ map specTypePB ars
specTypePB rvar@(RVar {}) = PolyBound rvar []
specTypePB r = error $ "specTypePB: Unexpected SpecType" ++ "\n" ++ show r


reftSymbol :: Reft -> LH.Symbol
reftSymbol = fst . unpackReft

unpackReft :: Reft -> (LH.Symbol, LH.Expr) 
unpackReft = coerce

----------------------------------------------------------------------------

generateRelTypes :: G2.Expr -> ([Type], Type)
generateRelTypes e =
    let
        ty_e = PresType $ inTyForAlls (typeOf e)
        arg_ty_c = filter (not . isTYPE)
                 . filter (notLH)
                 $ argumentTypes ty_e
        ret_ty_c = returnType ty_e
    in
    (arg_ty_c, ret_ty_c)
    where
        notLH ty
            | TyCon (Name n _ _ _) _ <- tyAppCenter ty = n /= "lh"
            | otherwise = True

typeToSort :: Type -> Maybe Sort
typeToSort (TyCon (Name n _ _ _) _) 
    | n == "Int"  = Just SortInt
    | n == "Double"  = Just SortDouble
typeToSort _ = Nothing

getLHMeasureName :: [GhcInfo] -> Name -> LH.Symbol
getLHMeasureName ghci (Name n m _ l) =
    let
        MeasureSymbols meas_symb = measureSymbols ghci
        zn = Name n m 0 l
    in
    case L.find (\meas -> symbolName meas == zn) meas_symb of
        Just meas -> meas
        Nothing -> error "getLHMeasureName: unhandled measure"

applicableMeasuresType :: Measures -> Type -> [(Name, Type)]
applicableMeasuresType meas =
    HM.toList . E.map' returnType . applicableMeasures meas

applicableMeasures :: Measures -> Type -> Measures
applicableMeasures meas t = E.filter (applicableMeasure t) meas 

applicableMeasure :: Type -> G2.Expr -> Bool
applicableMeasure t e =
    let
        te = filter notLH . argumentTypes . PresType . inTyForAlls $ typeOf e
    in
    case te of
        [te'] -> PresType t .:: te'
        _ -> False
    where
        notLH ty
            | TyCon (Name n _ _ _) _ <- tyAppCenter ty = n /= "lh"
            | otherwise = False

-- Helpers
allSynthSpec :: SpecInfo -> [SynthSpec]
allSynthSpec si = allPreSynthSpec si ++ allPostSynthSpec si

allPreSynthSpec :: SpecInfo -> [SynthSpec]
allPreSynthSpec = concatMap extractValues . s_syn_pre

allPostSynthSpec :: SpecInfo -> [SynthSpec]
allPostSynthSpec = extractValues . s_syn_post

allCNFs :: SpecInfo -> CNF
allCNFs si = allPreCoeffs si ++ allPostCoeffs si

allPreCoeffs :: SpecInfo -> CNF
allPreCoeffs = concatMap sy_coeffs . allPreSynthSpec

allPreSpecArgs :: SpecInfo -> [SpecArg]
allPreSpecArgs = concatMap sy_args_and_ret . allPreSynthSpec

allPostCoeffs :: SpecInfo -> CNF
allPostCoeffs = concatMap sy_coeffs . allPostSynthSpec

allPostSpecArgs :: SpecInfo -> [SpecArg]
allPostSpecArgs = concatMap sy_args_and_ret . allPostSynthSpec
