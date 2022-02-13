{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.Inference.Sygus.LiaSynth ( SynthRes (..)
                                          , Size
                                          , ModelNames (..)
                                          , liaSynth

                                          , MaxSize
                                          , incrMaxSize

                                          , BlockedModels
                                          , emptyBlockedModels
                                          , insertBlockedModel
                                          , blockedHashMap
                                          , unionBlockedModels) where

import G2.Data.Utils
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
import G2.Liquid.Inference.Sygus.FCConverter
import G2.Liquid.Inference.Sygus.SpecInfo

import G2.Solver as Solver

import Control.Monad
import Control.Monad.IO.Class 

import Language.Haskell.Liquid.Types as LH hiding (SP, ms, isBool)
import Language.Fixpoint.Types.Refinements as LH hiding (pAnd, pOr)
import qualified Language.Fixpoint.Types as LH
import qualified Language.Fixpoint.Types as LHF

import Data.Coerce
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T
import qualified Text.Builder as TB

liaSynth :: (InfConfigM m, ProgresserM m, MonadIO m, SMTConverter con ast out io)
         => con -> [GhcInfo] -> LiquidReadyState -> Evals Bool -> MeasureExs
         -> FuncConstraints
         -> BlockedModels -- ^ SMT Models to block being returned by the synthesizer at various sizes
         -> ToBeNames -> ToSynthNames -> m SynthRes
liaSynth con ghci lrs evals meas_ex fc blk_mdls to_be_ns ns_synth = do

    -- Figure out the type of each of the functions we need to synthesize
    let eenv = buildNMExprEnv $ expr_env . state $ lr_state lrs
        tenv = type_env . state $ lr_state lrs
        tc = type_classes . state $ lr_state lrs
        meas = lrsMeasures ghci lrs

    si <- buildSpecInfo eenv tenv tc meas ghci fc to_be_ns ns_synth

    liftIO . putStrLn $ "si = " ++ show si

    let meas = lrsMeasures ghci lrs

    MaxSize max_sz <- maxSynthSizeM

    synth con ghci eenv tenv meas meas_ex evals si fc blk_mdls 1

liaSynthOfSize :: (InfConfigM m, ProgresserM m) => Integer -> M.Map Name SpecInfo -> m (M.Map Name SpecInfo)
liaSynthOfSize sz m_si = do
    inf_c <- infConfigM
    MaxSize max_sz <- maxSynthSizeM
    let m_si' =
            M.map (\si -> 
                    let
                        s_syn_pre' =
                            map (mapPB
                                    (\psi ->
                                        psi { sy_coeffs = mkCNF (>= 1) sz (fromInteger max_sz) (sy_name psi) psi }
                                    )
                                 ) (s_syn_pre si)
                        s_syn_post' =
                            mapPB (\psi -> 
                                        psi { sy_coeffs = mkCNF (>= 1) sz (fromInteger max_sz) (sy_name psi) psi }
                                  ) (s_syn_post si)
                    in
                    si { s_syn_pre = s_syn_pre' -- (s_syn_pre si) { sy_coeffs = pre_c }
                       , s_syn_post = s_syn_post' -- (s_syn_post si) { sy_coeffs = post_c }
                       , s_max_coeff = if restrict_coeffs inf_c then 1 else 2 * sz }) m_si
    return m_si'
    where

mkCNF :: (Int -> Bool) -> Integer -> Int -> String -> SynthSpec -> CNF
mkCNF prd sz ms s psi_ =
    (if length (set_sy_args psi_) + length (set_sy_rets psi_) == 0
        then
          [ 
              (
                  s ++ "_c_coeff_act_" ++ show j
              ,
                   [ mkCoeffs prd s psi_ j k | k <- [1..sz] ] -- Ors
              )
          | j <-  [1..sz] ] -- Ands
        else [])
  ++
    (if length (set_sy_args psi_) + length (set_sy_rets psi_) > 0
        then
            [ 
                (
                    s ++ "_c_set_act_" ++ show j
                ,
                     [ mkSetForms prd ms s psi_ j k | k <- [1..sz] ] -- Ors
                )
            | j <-  [1..sz] ] -- Ands
        else [])
  ++
    (if length (bool_sy_args psi_) + length (bool_sy_rets psi_) > 0
        then
            [ 
                (
                    s ++ "_c_bool_act_" ++ show j
                ,
                     [ mkBoolForms prd sz ms s psi_ j k | k <- [1..sz] ] -- Ors
                )
            | j <-  [1..sz] ] -- Ands
        else [])


mkCoeffs :: (Int -> Bool) -> String -> SynthSpec -> Integer -> Integer -> Forms
mkCoeffs prd s psi j k =
    let
        ars = length (int_sy_args psi)
        rets = length (int_sy_rets psi)
    in
    LIA
        {
          c_active = s ++ "_f_act_" ++ show j ++ "_t_" ++ show k
        , c_op_branch1 = s ++ "_lia_op1_" ++ show j ++ "_t_" ++ show k
        , c_op_branch2 = s ++ "_lia_op2_" ++ show j ++ "_t_" ++ show k
        , b0 = s ++ "_b_" ++ show j ++ "_t_" ++ show k
        
        -- We only want solutions that have one or more return values with a
        -- non-zero coefficient.  Thus, if we have no return values, we
        -- don't need to consider any arguments
        , ars_coeffs =
            if prd rets
                then
                    [ s ++ "_a_c_" ++ show j ++ "_t_" ++ show k ++ "_a_" ++ show a
                    | a <- [1..ars]]
                else
                    []
        , rets_coeffs = 
            [ s ++ "_r_c_" ++ show j ++ "_t_" ++ show k ++ "_a_" ++ show a
            | a <- [1..rets]]
        }

mkSetForms :: (Int -> Bool) -> Int -> String -> SynthSpec -> Integer -> Integer -> Forms
mkSetForms prd max_sz s psi j k =
    let
        int_ars = length (int_sy_args psi)
        int_rets = length (int_sy_rets psi)

        ars = length (set_sy_args psi)
        rets = length (set_sy_rets psi)

        max_sets = min (ars + rets + int_ars + int_rets) 2 -- + max_sz - 1
    in
    Set
        { 
          c_active = s ++ "_s_act_" ++ show j ++ "_t_" ++ show k
        , c_op_branch1 = s ++ "_set_op1_" ++ show j ++ "_t_" ++ show k
        , c_op_branch2 = s ++ "_set_op2_" ++ show j ++ "_t_" ++ show k

        , int_sing_set_bools_lhs =
            if prd rets
                then
                    [ 
                      [ s ++ "_a_set_sing_lhs_" ++ show j ++ "_t_" ++ show k
                            ++ "_a_" ++ show a ++ "_int_" ++ show inter | inter <- [1..int_ars + int_rets]]
                    | a <- [1..max_sets]]
                else
                    []

        , int_sing_set_bools_rhs =
            if prd rets
                then
                    []
                    -- [ 
                    --   [ s ++ "_a_set_sing_rhs_" ++ show j ++ "_t_" ++ show k
                    --         ++ "_a_" ++ show a ++ "_int_" ++ show inter | inter <- [1..int_ars + int_rets]]
                    -- | a <- [1..ars + rets + max_sz - 1]]
                else
                    []

        , ars_bools_lhs =
            if prd rets
                then
                    [ 
                      [ s ++ "_a_set_lhs_" ++ show j ++ "_t_" ++ show k
                            ++ "_a_" ++ show a ++ "_int_" ++ show inter | inter <- [1..ars]]
                    | a <- [1..max_sets]]
                else
                    []
        , rets_bools_lhs = 
            [ [ s ++ "_r_set_lhs_" ++ show j ++ "_t_" ++ show k
                            ++ "_a_" ++ show a ++ "_int_" ++ show inter | inter <- [1..rets]]
            | a <- [1..ars + rets + max_sz - 1]]

        , ars_bools_rhs =
            if prd rets
                then
                    [ [ s ++ "_a_set_rhs_" ++ show j ++ "_t_" ++ show k
                            ++ "_a_" ++ show a ++ "_int_" ++ show inter | inter <- [1..ars]]
                    | a <- [1..max_sets]]
                else
                    []
        , rets_bools_rhs = 
            [[ s ++ "_r_set_rhs_" ++ show j ++ "_t_" ++ show k
                            ++ "_a_" ++ show a ++ "_int_" ++ show inter | inter <- [1..rets]]
            | a <- [1..max_sets]]
        }

mkBoolForms :: (Int -> Bool) -> Integer -> Int -> String -> SynthSpec -> Integer -> Integer -> Forms
mkBoolForms prd sz max_sz s psi j k =
    let
        ars = length (bool_sy_args psi)
        rets = length (bool_sy_rets psi)
    in
    BoolForm
        {
          c_active = s ++ "_bool_act_" ++ show j ++ "_t_" ++ show k
        , c_op_branch1 = s ++ "_bool_op1_" ++ show j ++ "_t_" ++ show k
        , c_op_branch2 = s ++ "_bool_op2_" ++ show j ++ "_t_" ++ show k

        , ars_bools =
            if prd rets
                then
                    [ s ++ "_a_bool_" ++ show j ++ "_t_" ++ show k ++ "_a_" ++ show a
                    | a <- [1..ars]]
                else
                    []
        , rets_bools = 
            [ s ++ "_r_bool_" ++ show j ++ "_t_" ++ show k ++ "_a_" ++ show a
            | a <- [1..rets]]

        , forms = concat
                . map snd
                $ mkCNF (const True) sz max_sz (s ++ "_bool_" ++ show j ++ "_t_" ++ show k ++ "_" )
                        (psi { sy_args = filter (not . isBool . smt_sort) (sy_args psi)
                             , sy_rets = filter (not . isBool . smt_sort) (sy_rets psi) })
        }
        where
            isBool SortBool = True
            isBool _ = False

synth :: (InfConfigM m, ProgresserM m, MonadIO m, SMTConverter con ast out io)
      => con
      -> [GhcInfo]
      -> NMExprEnv
      -> TypeEnv
      -> Measures
      -> MeasureExs
      -> Evals Bool
      -> M.Map Name SpecInfo
      -> FuncConstraints
      -> BlockedModels
      -> Size
      -> m SynthRes
synth con ghci eenv tenv meas meas_ex evals si fc blk_mdls sz = do
    si' <- liaSynthOfSize sz si
    let zero_coeff_hdrs = softCoeffAssertZero si' ++ softClauseActAssertZero si' -- ++ softFuncActAssertZero si'
        -- zero_coeff_hdrs = softFuncActAssertZero si' ++ softClauseActAssertZero si'
        -- zero_coeff_hdrs = softCoeffAssertZero si' -- softFuncActAssertZero si' ++ softClauseActAssertZero si'

        max_coeffs_cons = maxCoeffConstraints si'
        soft_coeff_cons = softCoeffConstraints si'

        soft_set_bool_cons = softSetConstraints si'

        mdls = lookupBlockedModels sz blk_mdls
        rel_mdls = map (uncurry (filterModelToRel si')) mdls
        block_mdls = map blockModelDirectly rel_mdls

        non_equiv_mdls = lookupNonEquivBlockedModels sz blk_mdls
        rel_non_equiv_mdls = map (uncurry (filterModelToRel si')) non_equiv_mdls
        fun_block_mdls = concatMap (uncurry (blockModelWithFuns si')) $ zip (map show ([0..] :: [Integer])) rel_non_equiv_mdls

        ex_assrts =    [Comment "favor making coefficients 0"]
                    ++ zero_coeff_hdrs
                    ++ [Comment "enforce maximal and minimal values for coefficients"]
                    ++ max_coeffs_cons
                    ++ [Comment "favor coefficients being -1, 0, or 1"]
                    ++ soft_coeff_cons
                    ++ [Comment "favor set booleans being false"]
                    ++ soft_set_bool_cons
                    ++ [Comment "block spurious models"]
                    ++ block_mdls

        drop_if_unknown = [Comment "stronger blocking of spurious models"] ++ fun_block_mdls

    MaxSize max_sz <- maxSynthSizeM

    res <- synth' con ghci eenv tenv meas meas_ex evals si' fc ex_assrts drop_if_unknown blk_mdls sz
    case res of
        SynthEnv _ _ (Just n_mdl) _ _ -> do
            new  <- checkModelIsNewFunc con si' n_mdl non_equiv_mdls
            case new of
                Nothing -> return res
                Just (_, eq_mdl) -> do
                    let sys = concatMap allSynthSpec $ M.elems si'
                        rel_n_mdl = filterIrrelByConstruction sys n_mdl
                        rel_eq_mdl = filterIrrelByConstruction sys eq_mdl

                        mn = determineRelSynthSpecs si' rel_n_mdl rel_eq_mdl
                        mdls' = foldr (\n -> insertEquivBlockedModel sz (MNOnlySMTNames [n]) n_mdl) blk_mdls mn

                    liftIO . putStrLn $ "mn = " ++ show mn
                    synth con ghci eenv tenv meas meas_ex evals si fc mdls' sz
        SynthFail _
            | sz < max_sz -> synth con ghci eenv tenv meas meas_ex evals si fc blk_mdls (sz + 1)
            | otherwise -> return res
    
synth' :: (InfConfigM m, ProgresserM m, MonadIO m, SMTConverter con ast out io)
       => con
       -> [GhcInfo]
       -> NMExprEnv
       -> TypeEnv
       -> Measures
       -> MeasureExs
       -> Evals Bool
       -> M.Map Name SpecInfo
       -> FuncConstraints
       -> [SMTHeader]
       -> [SMTHeader]
       -> BlockedModels
       -> Size
       -> m SynthRes
synth' con ghci eenv tenv meas meas_ex evals m_si fc headers drop_if_unknown blk_mdls sz = do
    let n_for_m = namesForModel m_si
    liftIO $ print m_si
    let consts = arrayConstants m_si
    (constraints, nm_fc_map) <- nonMaxCoeffConstraints ghci eenv tenv meas meas_ex evals m_si fc
    let hdrs = consts ++ constraints ++ headers ++ drop_if_unknown

    liftIO $ if not (null drop_if_unknown) then putStrLn "non empty drop_if_unknown" else return ()

    mdl <- liftIO $ constraintsToModelOrUnsatCore con hdrs n_for_m

    case mdl of
        SAT mdl' -> do
            let gs' = modelToGS m_si mdl'
            liftIO $ print gs'
            return (SynthEnv gs' sz (Just mdl') blk_mdls Nothing)
        UNSAT uc ->
            let
                fc_uc = fromSingletonFC . NotFC . AndFC . map (nm_fc_map HM.!) $ HS.toList uc
            in
            return (SynthFail fc_uc)
        Unknown _
            | not (null drop_if_unknown) ->
                synth' con ghci eenv tenv meas meas_ex evals m_si fc headers [] blk_mdls sz
            | otherwise -> error "synth': Unknown"

----------------------------------------------------------------------------
-- Blocking Models building/manipulation

namesForModel :: M.Map Name SpecInfo -> [(SMTName, Sort)]
namesForModel = concat . map siNamesForModel . M.elems

siNamesForModel :: SpecInfo -> [(SMTName, Sort)]
siNamesForModel si
    | s_status si == Synth = concatMap sySpecNamesForModel $ allSynthSpec si
    | otherwise = []

sySpecNamesForModel :: SynthSpec -> [(SMTName, Sort)]
sySpecNamesForModel sys =
    let
        all_coeffs = zip (sySpecGetCoeffs sys) (repeat SortInt)
        all_set_bools = zip (sySpecGetSetBools sys) (repeat SortBool)
        all_bool_bools = zip (sySpecGetBoolBools sys) (repeat SortBool)
        all_acts = zip (sySpecGetActs sys) (repeat SortInt)
        all_op_branch = zip (sySpecGetOpBranches sys) (repeat SortBool)
    in
    all_coeffs ++ all_set_bools ++ all_bool_bools ++ all_acts ++ all_op_branch

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
        sys = case ns of
                MNAll  -> concatMap allSynthSpec $ M.elems m_si
                MNOnly ns' -> concatMap allSynthSpec $ mapMaybe (flip M.lookup m_si) ns'
                MNOnlySMTNames ns' -> filter (\sy -> sy_name sy `elem` ns')
                                    . concatMap allSynthSpec
                                    $ M.elems m_si
        vs = map fst $ concatMap sySpecNamesForModel sys
    in
    filterIrrelByConstruction sys $ M.filterWithKey (\n _ -> n `elem` vs) mdl

filterIrrelByConstruction :: Foldable f => f SynthSpec -> SMTModel -> SMTModel
filterIrrelByConstruction = flip (foldr filterIrrelByConstruction')

filterIrrelByConstruction' :: SynthSpec -> SMTModel -> SMTModel
filterIrrelByConstruction' sys = 
      filterClauseActiveBooleans sys
    . filterCoeffActiveBooleans sys
    . filterRelOpBranch sys

-- If the clause level boolean is set to true, we remove all the
-- formula level active booleans, since the formulas are
-- irrelevant.
filterClauseActiveBooleans :: SynthSpec -> SMTModel -> SMTModel
filterClauseActiveBooleans si mdl =
    let
        clauses = sy_coeffs si
    in
    foldr (\(cl_act, cfs) mdl_ -> if
              | M.lookup cl_act mdl_ == Just (VBool True) ->
                  foldr (\c -> M.delete (c_active c)) mdl_ cfs
              | otherwise -> mdl_) mdl clauses

-- If the formula level active booleans are set to false, we remove all the
-- coefficients in the formula, since the formula is now irrelevant.
filterCoeffActiveBooleans :: SynthSpec -> SMTModel -> SMTModel
filterCoeffActiveBooleans si mdl =
    let
        clauses = sy_coeffs si
        cffs = concatMap snd clauses
    in
    foldr (\cf mdl_ -> if
              | M.lookup (c_active cf) mdl_ == Just (VBool False) ->
                foldr M.delete mdl_ (coeffs cf)
              | otherwise -> mdl_) mdl cffs


filterRelOpBranch :: SynthSpec -> SMTModel -> SMTModel
filterRelOpBranch si mdl =
    let
        clauses = sy_coeffs si
        coeffs = concatMap snd clauses
    in
    -- If we are not using a clause, we don't care about c_op_branch1 and c_op_branch2
    -- If we are using a clause but c_op_branch1 is true, we don't care about c_op_branch2
    foldr (\form mdl_ -> if
              | M.lookup (c_active form) mdl == Just (VBool False) ->
                  M.delete (c_op_branch2 form) $ M.delete (c_op_branch1 form) mdl_
              | M.lookup (c_op_branch1 form) mdl == Just (VBool True) ->
                  M.delete (c_op_branch2 form) mdl_
              | otherwise -> mdl) mdl coeffs

-- | Create specification definitions corresponding to previously rejected models,
-- and add assertions that the new synthesized specification definition must
-- have a different output than the old specifications at at least one point.
-- Because this requires a symbolic point being input into the synthesized function
-- (with symbolic coefficients) this requires (undecidable) non linear arithmetic (NIA).
blockModelWithFuns :: M.Map Name SpecInfo -> String -> SMTModel -> [SMTHeader]
blockModelWithFuns si s mdl =
    let
        e_si = M.elems $ M.filter (\si' -> s_status si' == Synth) si

        vrs = map (uncurry blockVars) $ zip (map (\i -> s ++ "_" ++ show i) ([0..] :: [Integer])) e_si
        var_defs = concatMap varDefs vrs

        si_nsi =   map (\(i, si') -> (si', renameByAdding i si'))
                 . zip (map (\i -> s ++ "_" ++ show i) ([0..] :: [Integer]))
                 $ e_si

        fun_defs = concatMap (defineModelLIAFuns mdl . snd) si_nsi

        eqs = map (\(vs, (si', nsi')) -> mkEqualityAST vs si' nsi') $ zip vrs si_nsi

        neq = [Solver.Assert . (:!) $ mkSMTAnd eqs]
    
    in
    var_defs ++ fun_defs ++ neq

----------------------------------------------------------------------------
-- Blocking Models via checking after the fact

-- | Checks that the first model and each model in the list have at least
-- one point that they classifies differently,
-- i.e. for each model in the list, there must be at least one point that is
-- classified as true by that model, but false by the first model (or vice versa.)
-- As opposed to `blockModelWithFuns`, which enforced this as a constraint when
-- synthesizing the new specification, this function acts as a check on a newly
-- synthesized specification.
-- This avoids the need for non linear arithmetic, but allows us to quickly
-- reject newly synthesized specifications that are identical to some previous
-- specifications.
checkModelIsNewFunc :: (MonadIO m, SMTConverter con ast out io) => con -> M.Map Name SpecInfo -> SMTModel -> [(ModelNames, SMTModel)] -> m (Maybe (ModelNames, SMTModel))
checkModelIsNewFunc _ _ _ [] = return Nothing
checkModelIsNewFunc con si mdl ((mdl_nm, mdl'):mdls) = do
    b' <- checkModelIsNewFunc' con si mdl mdl'
    case b' of
        True -> checkModelIsNewFunc con si mdl mdls
        False -> do
            liftIO $ do
                putStrLn "Equiv!"
                print mdl_nm
                print mdl
                print mdl'
                putStrLn $ "diff 1 = " ++ show (M.toList mdl' L.\\ M.toList mdl)
                putStrLn $ "diff 2 = " ++ show (M.toList mdl L.\\ M.toList mdl')
            return (Just (mdl_nm, mdl'))

checkModelIsNewFunc' :: (MonadIO m, SMTConverter con ast out io) => con -> M.Map Name SpecInfo -> SMTModel -> SMTModel -> m Bool
checkModelIsNewFunc' con si mdl1 mdl2 = do
    let e_si = M.elems $ M.filter (\si' -> s_status si' == Synth) si

        vrs = map (uncurry blockVars) $ zip (map (\i -> "_c_" ++ show i) ([0..] :: [Integer])) e_si
        var_defs = concatMap varDefs vrs

        si_nsi = map (\(i, si') -> (si', renameByAdding i si'))
               . zip (map (\i -> "_c_" ++ show i) ([0..] :: [Integer]))
               $ e_si

        fun_defs1 = concatMap (defineModelLIAFuns mdl1 . fst) si_nsi
        fun_defs2 = concatMap (defineModelLIAFuns mdl2 . snd) si_nsi

        eqs = map (\(vs, (si', nsi')) -> mkEqualityAST vs si' nsi') $ zip vrs si_nsi

        neq = [Solver.Assert . (:!) $ mkSMTAnd eqs]
    
        hdrs = arrayConstants si ++ var_defs ++ fun_defs1 ++ fun_defs2 ++ neq

    r <- liftIO $ checkConstraints con hdrs
    case r of
        SAT _ -> return True
        UNSAT _ -> return False
        Unknown _ -> error "checkModelIsNewFunc': unknown result"

defineModelLIAFuns :: SMTModel -> SpecInfo -> [SMTHeader]
defineModelLIAFuns mdl si =
    let
        fs = L.nubBy (\si1 si2 -> sy_name si1 == sy_name si2)
           $ (extractValues $ s_syn_post si) ++ (concatMap extractValues $ s_syn_pre si)
    in
    if s_status si == Synth
        then map (defineModelLIAFuncSF mdl) fs
        else []

defineModelLIAFuncSF :: SMTModel -> SynthSpec -> SMTHeader
defineModelLIAFuncSF mdl sf = 
    let
        ars_nm = map smt_var (sy_args_and_ret sf)
        ars = zip ars_nm (map smt_sort $ sy_args_and_ret sf)
    in
    DefineFun (sy_name sf) ars SortBool (buildLIA_SMT_fromModel mdl sf)

renameByAdding :: String -> SpecInfo -> SpecInfo
renameByAdding i si =
    si { s_syn_pre = map (mapPB rn) $ s_syn_pre si
       , s_syn_post = mapPB rn $ s_syn_post si
       }
    where
        rn s = s { sy_name = sy_name s ++ "_MDL_" ++ i }

buildLIA_SMT_fromModel :: SMTModel -> SynthSpec -> SMTAST
buildLIA_SMT_fromModel mdl sf =
    buildSpec (:+) (:*) (.=.) (.=.) (:>) (:>=) Ite Ite
              mkSMTAnd mkSMTAnd mkSMTOr
              mkSMTUnion mkSMTIntersection smtSingleton
              mkSMTIsSubsetOf (flip ArraySelect)
              vint VInt vbool vset
              falseArray
              trueArray
              sf 
    where
        vint n
            | Just v <- M.lookup n mdl = v
            | otherwise = V n SortInt

        vbool n
            | Just v <- M.lookup n mdl = v
            | otherwise = V n SortBool

        vset n
            | Just v <- M.lookup n mdl = v
            | otherwise = V n (SortArray SortInt SortBool)

smtSingleton :: SMTAST -> SMTAST
smtSingleton mem = ArrayStore falseArray mem (VBool True)

blockVars :: String -> SpecInfo -> ([PolyBound [(SMTName, Sort)]], PolyBound [(SMTName, Sort)])
blockVars str si = ( map (uncurry mk_blk_vars) . zip (map show ([0..] :: [Integer])) $ s_syn_pre si
                   , mk_blk_vars "r" $ s_syn_post si)
    where
        mk_blk_vars i sy_s =
            mapPB (\(j, s) -> 
                        map (\(k, sa) ->
                                ("x_MDL_" ++ str ++ "_" ++ i ++ "_" ++ show j ++ "_" ++ show k, smt_sort sa))
                      . zip ([0..] :: [Integer])
                      $ sy_args_and_ret s
                  )
            $ zipPB (uniqueIds sy_s) sy_s

varDefs :: ([PolyBound [(SMTName, Sort)]], PolyBound [(SMTName, Sort)]) -> [SMTHeader]
varDefs = map (\(n, srt) -> VarDecl (TB.text . T.pack $ n) srt)
        . concat
        . concatMap extractValues
        . (\(x, y) -> y:x)

mkEqualityAST :: ([PolyBound [(SMTName, Sort)]], PolyBound [(SMTName, Sort)]) -> SpecInfo -> SpecInfo -> SMTAST
mkEqualityAST (avs, rvs) si nsi =
    let
        avs' = map (mapPB (map fst)) avs
        rvs' = mapPB (map fst) rvs

        pre_eq =
            map (mapPB (uncurry3 mkFuncEq) . uncurry3 zip3PB)
            $ zip3 avs' (s_syn_pre si) (s_syn_pre nsi)

        pre_eq' = concatMap extractValues pre_eq

        post_eq =
            mapPB (uncurry3 mkFuncEq) $ zip3PB rvs' (s_syn_post si) (s_syn_post nsi)

        post_eq' = extractValues post_eq
    in
    mkSMTAnd (post_eq' ++ pre_eq')

mkFuncEq :: [SMTName] -> SynthSpec -> SynthSpec -> SMTAST
mkFuncEq vs s_sp ns_sp = 
    let
        smt_vs = map (flip V SortInt) vs
    in
    Func (sy_name s_sp) smt_vs := Func (sy_name ns_sp) smt_vs

-- Determines which function specs have been assigned different values in the two models.
determineRelFuncs :: M.Map Name SpecInfo -> SMTModel -> SMTModel -> [Name]
determineRelFuncs m_si mdl1 mdl2 =
    let
        diff = M.keys 
             $ M.differenceWith (\v1 v2 -> case v1 == v2 of
                                                True -> Nothing
                                                False -> Just v1) mdl1 mdl2
    in
      M.keys
    $ M.filter 
        (\si -> any (\n -> n `elem` diff) . map fst $ siNamesForModel si)
        m_si

-- Determines which SynthSpecs have been assigned different values in the two models.
determineRelSynthSpecs :: M.Map Name SpecInfo -> SMTModel -> SMTModel -> [SMTName]
determineRelSynthSpecs m_si mdl1 mdl2 =
    let
        diff = M.keys 
             $ M.differenceWith (\v1 v2 -> case v1 == v2 of
                                                True -> Nothing
                                                False -> Just v1) mdl1 mdl2
    in
      map sy_name
    . filter 
        (\sys -> any (\n -> n `elem` diff) . map fst $ sySpecNamesForModel sys)
    . concatMap allSynthSpec 
    $ M.elems m_si

-- computing F_{Fixed}, i.e. what is the value of known specifications at known points 
envToSMT :: MeasureExs -> Evals (Integer, Bool)  -> M.Map Name SpecInfo -> FuncConstraints
         -> ([SMTHeader], HM.HashMap SMTName FuncConstraint)
envToSMT meas_ex evals si fc =
    let
        nm_fc = zip ["f" ++ show i | i <- ([1..] :: [Integer])]
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

                -- In the case that we get an unsat core, we are only interested in knowing which specifications
                -- that have already been chosen must be changed.  Thus, we only name those pieeces of the environment.
                named = case s_status si of
                            Known -> Named
                            _ -> \x _ -> x
            in
            [ (named pre pre_name, (pre_name, pre_real))
            , (named post post_name, (post_name, post_real))]
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
                          Solver.Assert (((:!) $ V act SortBool)
                        :=> 
                          mkSMTOr (concatMap (\c -> mkCoeffRetNonZero c) cff))
                  ) cffs
              ) sy_sps

mkCoeffRetNonZero :: Forms -> [SMTAST]
mkCoeffRetNonZero cffs@(LIA {}) =
    let
        act = c_active cffs
        ret_cffs = rets_coeffs cffs
    in
    case null ret_cffs of
        True -> [VBool True]
        False -> 
            [V act SortBool :=> mkSMTOr (map (\r -> V r SortInt :/= VInt 0) ret_cffs)]
mkCoeffRetNonZero cffs@(Set {}) =
    let
        act = c_active cffs
        ret_bools = concat $ rets_bools_lhs cffs ++ rets_bools_rhs cffs
    in
    case null ret_bools of
        True -> [VBool True]
        False -> 
            [V act SortBool :=> mkSMTOr (map (\r -> V r SortBool) ret_bools)]
mkCoeffRetNonZero cffs@(BoolForm {}) =
    let
        act = c_active cffs
        ret_bools = rets_bools cffs
    in
    case null ret_bools of
        True -> [VBool True]
        False -> 
            [V act SortBool :=> mkSMTOr (map (\r -> (:!) (V r SortBool)) ret_bools)]

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
-- (3) If the n^th "or" is deactivated (by it's boolean being true),
-- then the n + 1^th "or" must also be deactivated 
-- (4) If the n^th "and" is deactivated (by it's boolean being false),
-- then the n + 1^th "and" must also be deactivated 
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

        -- (3)
        or_acts = map (map (map fst) . allCNFsSeparated) a_si :: [[[SMTName]]]
        or_neighbors_deact =
            concatMap 
              (concatMap 
                (map (\(n1, n2) -> ((:!) $ V n2 SortBool) :=> ((:!) $ V n1 SortBool)) . neighbors)
              ) $ or_acts

        -- (4)
        and_neighbors_deact =  and_block (\case LIA {} -> True; _ -> False) a_si
                            ++ and_block (\case Set {} -> True; _ -> False) a_si
    in
    map Solver.Assert $ cl_imp_coeff ++ coeff_act_imp_zero -- ++ or_neighbors_deact ++ and_neighbors_deact
    where
        neighbors [] = []
        neighbors [_] = []
        neighbors (x:xs@(y:_)) = (x, y):neighbors xs

        and_block p a_si' = 
            let
                and_acts = concatMap (map (map snd) . allCNFsSeparated) a_si'
            in
            concatMap 
              (concatMap 
                  ( mapMaybe 
                      (\(n1, n2) -> if p n1 && p n2
                                        then Just (V (c_active n2) SortBool :=> V (c_active n1) SortBool)
                                        else Nothing)
                  . neighbors
                  )
              ) $ and_acts

softCoeffAssertZero :: M.Map Name SpecInfo -> [SMTHeader]
softCoeffAssertZero = map (\n -> AssertSoft (V n SortInt := VInt 0) (Just "minimal_size")) . getCoeffs

softFuncActAssertZero :: M.Map Name SpecInfo -> [SMTHeader]
softFuncActAssertZero = map (\n -> AssertSoft ((:!) $ V n SortBool) (Just "minimal_size")) . getFuncActs

softClauseActAssertZero :: M.Map Name SpecInfo -> [SMTHeader]
softClauseActAssertZero = map (\n -> AssertSoft (V n SortBool) (Just "minimal_size")) . getClauseActs

maxCoeffConstraints :: M.Map Name SpecInfo -> [SMTHeader]
maxCoeffConstraints = maxCoeffConstraints' Solver.Assert s_max_coeff

softCoeffConstraints :: M.Map Name SpecInfo -> [SMTHeader]
softCoeffConstraints = maxCoeffConstraints' (flip Solver.AssertSoft (Just "coeff")) (const 1)

maxCoeffConstraints' :: (SMTAST -> SMTHeader) -> (SpecInfo -> Integer) -> M.Map Name SpecInfo -> [SMTHeader]
maxCoeffConstraints' to_header max_c =
      map to_header
    . concatMap
        (\si ->
            let
                cffs = concatMap coeffs . concatMap snd $ allPreCoeffs si ++ allPostCoeffs si
            in
            if s_status si == Synth
                then map (\c -> (Neg (VInt (max_c si)) :<= V c SortInt)
                                    .&&. (V c SortInt :<= VInt (max_c si))) cffs
                else []) . M.elems

softSetConstraints :: M.Map Name SpecInfo -> [SMTHeader]
softSetConstraints =
    map (\n -> AssertSoft ((:!) (V n SortBool)) (Just "minimal_sets")) . getSetBools

arrayConstants :: M.Map Name SpecInfo -> [SMTHeader]
arrayConstants si =
  let
    frms = concatMap allForms $ M.elems si
  in
  if any (\case Set {} -> True; _ -> False) frms
      then
          [ VarDecl (TB.text "true_array") (SortArray SortInt SortBool)
          , Solver.Assert (trueArray := (mkSMTUniversalArray SortInt SortBool))
          , VarDecl (TB.text "false_array") (SortArray SortInt SortBool)
          , Solver.Assert (falseArray := (mkSMTEmptyArray SortInt SortBool))]
      else []

trueArray :: SMTAST
trueArray = V "true_array" (SortArray SortInt SortBool)

falseArray :: SMTAST
falseArray = V "false_array" (SortArray SortInt SortBool)

nonMaxCoeffConstraints :: (InfConfigM m, ProgresserM m) => [GhcInfo] -> NMExprEnv -> TypeEnv -> Measures -> MeasureExs -> Evals Bool  -> M.Map Name SpecInfo -> FuncConstraints
                       -> m ([SMTHeader], HM.HashMap SMTName FuncConstraint)
nonMaxCoeffConstraints ghci eenv tenv meas meas_ex evals m_si fc = do
    let evals' = assignIds evals
        
        all_acts = getActs m_si
        all_coeffs = getCoeffs m_si
        all_set_bools = getSetBools m_si
        all_bool_bools = getBoolBools m_si
        get_ops = getOpBranches m_si

        var_act_hdrs = map (flip VarDecl SortBool . TB.text . T.pack) $ L.nub all_acts
        var_int_hdrs = map (flip VarDecl SortInt . TB.text . T.pack) $ L.nub all_coeffs
        var_bool_set_hdrs = map (flip VarDecl SortBool . TB.text . T.pack) $ L.nub all_set_bools
        var_bool_bool_hdrs = map (flip VarDecl SortBool . TB.text . T.pack) $ L.nub all_bool_bools
        var_op_hdrs = map (flip VarDecl SortBool . TB.text . T.pack) $ L.nub get_ops

        def_funs = concatMap defineLIAFuns $ M.elems m_si
        (env_smt, nm_fc) = envToSMT meas_ex evals' m_si fc

        ret_is_non_zero = mkRetNonZero m_si

        lim_equiv_smt = limitEquivModels m_si

        poly_access = polyAccessConstraints2 ghci meas m_si
    
    fc_smt <- constraintsToSMT eenv tenv meas meas_ex evals' m_si fc

    return
        (    var_act_hdrs
          ++ var_int_hdrs
          ++ var_bool_set_hdrs
          ++ var_bool_bool_hdrs
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
          ++ [Comment "polymorphic access constraints"]
          ++ poly_access
        , nm_fc)

constraintsToSMT :: (InfConfigM m, ProgresserM m) =>
                     NMExprEnv
                  -> TypeEnv
                  -> Measures
                  -> MeasureExs
                  -> Evals (Integer, Bool)
                  -> M.Map Name SpecInfo
                  -> FuncConstraints
                  -> m [SMTHeader]
constraintsToSMT eenv tenv meas meas_ex evals si fc =
    return . map (Solver.Assert) =<<
        convertConstraints 
                    convertExprToSMT
                    (ifNotNull mkSMTAnd (VBool True))
                    (ifNotNull mkSMTOr (VBool False))
                    (:!)
                    (:=>)
                    Func
                    (\n i _ -> Func n [VInt i])
                    (\n i _ -> Func n [VInt i])
                    eenv tenv meas meas_ex evals si fc
    where
        ifNotNull _ def [] = def
        ifNotNull f _ xs = f xs

convertExprToSMT :: G2.Expr -> SMTAST
convertExprToSMT e = 
    case e of
        (App (App (Data (DataCon (Name n _ _ _) _)) _) ls)
            | Just is <- extractInts ls ->
                foldr (\i arr -> ArrayStore arr (VInt i) (VBool True)) falseArray is
        _ -> exprToSMT e

extractInts :: G2.Expr -> Maybe [Integer]
extractInts (App (App (App (Data _ ) (Type _)) (App _ (Lit (LitInt i)))) xs) =
    return . (i:) =<< extractInts xs
extractInts (App (Data _) _) = Just []
extractInts e = Nothing

---

getCoeffs :: M.Map Name SpecInfo -> [SMTName]
getCoeffs = concatMap siGetCoeffs . M.elems

sySpecGetCoeffsNoB :: SynthSpec -> [SMTName]
sySpecGetCoeffsNoB = concatMap coeffsNoB . concatMap snd . sy_coeffs

siGetCoeffs :: SpecInfo -> [SMTName]
siGetCoeffs si
    | s_status si == Synth = concatMap sySpecGetCoeffs $ allSynthSpec si
    | otherwise = []

sySpecGetCoeffs :: SynthSpec -> [SMTName]
sySpecGetCoeffs = concatMap coeffs . concatMap snd . sy_coeffs

getSetBools :: M.Map Name SpecInfo -> [SMTName]
getSetBools = concatMap siGetSetBools . M.elems

siGetSetBools :: SpecInfo -> [SMTName]
siGetSetBools si
    | s_status si == Synth = concatMap sySpecGetSetBools $ allSynthSpec si
    | otherwise = []

sySpecGetSetBools :: SynthSpec -> [SMTName]
sySpecGetSetBools = concatMap setBools . concatMap snd . sy_coeffs

getBoolBools :: M.Map Name SpecInfo -> [SMTName]
getBoolBools = concatMap siGetBoolBools . M.elems 

siGetBoolBools :: SpecInfo -> [SMTName]
siGetBoolBools si
    | s_status si == Synth = concatMap sySpecGetBoolBools $ allSynthSpec si
    | otherwise = []

sySpecGetBoolBools :: SynthSpec -> [SMTName]
sySpecGetBoolBools = concatMap boolBools . concatMap snd . sy_coeffs

---

getOpBranches:: M.Map Name SpecInfo -> [SMTName]
getOpBranches = concatMap siGetOpBranches . M.elems

siGetOpBranches :: SpecInfo -> [SMTName]
siGetOpBranches si
    | s_status si == Synth =
        concatMap sySpecGetOpBranches $ allSynthSpec si
    | otherwise = []

sySpecGetOpBranches :: SynthSpec -> [SMTName]
sySpecGetOpBranches = concatMap sySpecGetOpBranchesForm . concatMap snd . sy_coeffs

sySpecGetOpBranchesForm :: Forms -> [SMTName]
sySpecGetOpBranchesForm c@(BoolForm {}) =
    [c_op_branch1 c, c_op_branch2 c] ++ concatMap sySpecGetOpBranchesForm (forms c)
sySpecGetOpBranchesForm c = [c_op_branch1 c, c_op_branch2 c]
---

sySpecGetActs :: SynthSpec -> [SMTName]
sySpecGetActs sys = sySpecGetClauseActs sys ++ sySpecGetFuncActs sys

sySpecGetClauseActs :: SynthSpec -> [SMTName]
sySpecGetClauseActs = map fst . sy_coeffs

sySpecGetFuncActs :: SynthSpec -> [SMTName]
sySpecGetFuncActs = concatMap formActives . concatMap snd . sy_coeffs

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
    | s_status si == Synth = concatMap formActives . concatMap snd $ allCNFs si
    | otherwise = []

formActives :: Forms -> [SMTName]
formActives cffs@(BoolForm {}) = c_active cffs:concatMap formActives (forms cffs)
formActives cffs = [c_active cffs]

defineLIAFuns :: SpecInfo -> [SMTHeader]
defineLIAFuns si =
    (if s_status si == Synth
        then
            let
                funcs = L.nubBy (\si1 si2 -> sy_name si1 == sy_name si2)
                      $ (extractValues $ s_syn_post si) ++ (concatMap extractValues $ s_syn_pre si)
            in
            map defineSynthLIAFuncSF funcs
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
        ars = zip ars_nm (map smt_sort $ sy_args_and_ret sf)
    in
    DefineFun (sy_name sf) ars SortBool (buildLIA_SMT sf)

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

type IsSubsetOf a b = a -> a -> b
type IsMember a b = a -> a -> b

type Union a = a -> a -> a
type Intersection a = a -> a -> a

type Singleton a = a -> a

type VInt a = SMTName -> a
type CInt a = Integer -> a
type VBool b = SMTName -> b
type VSet s = SMTName -> s
type EmptySet s = s
type UniversalSet s = s

buildLIA_SMT :: SynthSpec -> SMTAST
buildLIA_SMT sf =
    buildSpec (:+) (:*) (.=.) (.=.) (:>) (:>=) Ite Ite
              mkSMTAnd mkSMTAnd mkSMTOr mkSMTUnion mkSMTIntersection smtSingleton
              mkSMTIsSubsetOf (flip ArraySelect)
              (flip V SortInt) VInt (flip V SortBool) (flip V $ SortArray SortInt SortBool)
              falseArray
              trueArray
              sf

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
        post_ars = allPostSpecArgs si

        build ars = buildSpec ePlus eTimes
                              bEq bIff bGt bGeq
                              eIte eIte id
                              pAnd pOr
                              eUnion eIntersection eSingleton
                              bIsSubset bIsMember
                              (detVar ars) (ECon . I) (detBool ars)
                              (detSet ars) eEmptySet eUnivSet
        pre = map (mapPB (\psi -> build (all_sy_args_and_ret psi) psi)) $ s_syn_pre si
        post = mapPB (build post_ars) $ s_syn_post si
    in
    pre ++ [post]
    where
        detVar ars v 
            | Just (VInt c) <- M.lookup v mv = ECon (I c)
            | Just sa <- L.find (\sa_ -> v == smt_var sa_) ars = lh_rep sa
            | otherwise = error "detVar: variable not found"

        detBool ars v
            | Just (VBool b) <- M.lookup v mv = if b then PTrue else PFalse
            | Just sa <- L.find (\sa_ -> v == smt_var sa_) ars = lh_rep sa
            | otherwise = error $ "detBool: variable not found" ++ " " ++ show v ++ "\nars = " ++ show ars

        detSet ars v
            | Just sa <- L.find (\sa_ -> v == smt_var sa_) ars = lh_rep sa
            | otherwise = error "detSet: variable not found"

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
        eIte _ _ _ = error "eIte: Should never have non-concrete bool"

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
            | x == eUnivSet
            , y == eUnivSet = PTrue
            | x == eUnivSet || y == eUnivSet = PFalse
            | otherwise = PAtom LH.Eq x y

        bIff x y
            | x == y = PTrue
            | otherwise = PIff x y


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

        eUnion x y
            | x == eEmptySet = y
            | y == eEmptySet = x
            | x == eUnivSet = eUnivSet
            | y == eUnivSet = eUnivSet
            | x == y = x
            | otherwise = EApp (EApp (EVar "Set_cup") x) y
        
        eIntersection x y
            | x == eUnivSet = y
            | y == eUnivSet = x
            | x == eEmptySet = eEmptySet
            | y == eEmptySet = eEmptySet
            | x == y = x
            | otherwise = EApp (EApp (EVar "Set_cap") x) y

        eSingleton = EApp (EVar "Set_sng")

        bIsSubset x y
            | x == eEmptySet = PTrue
            | y == eUnivSet = PTrue
            | x == eUnivSet = PFalse
            | x == y = PTrue
            | otherwise = EApp (EApp (EVar "Set_sub") x) y

        bIsMember x y
            | y == eEmptySet = PFalse
            | y == eUnivSet = PTrue
            | otherwise = EApp (EApp (EVar "Set_mem") x) y

        eEmptySet = EApp (EVar "Set_empty") (ECon (I 0))
        eUnivSet = EVar ("Set_univ")

raiseSpecs :: PolyBound SynthSpec -> PolyBound [LH.Expr] -> PolyBound [LH.Expr]
raiseSpecs sy_sp pb =
    let
        symb_pb = mapPB (HS.unions . map (argsInExpr . lh_rep) . int_sy_args_and_ret) sy_sp
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


buildSpec :: Show b => Plus a
          -> Mult a
          -> EqF a b
          -> EqF b b
          -> Gt a b
          -> GEq a b
          -> Ite b b 
          -> Ite b a
          -> And b c
          -> And b b
          -> Or b

          -> Union a
          -> Intersection a
          -> Singleton a
          -> IsSubsetOf a b
          -> IsMember a b

          -> VInt a
          -> CInt a
          -> VBool b
          -> VSet a
          -> EmptySet a
          -> UniversalSet a
          -> SynthSpec
          -> c
buildSpec plus mult eq eq_bool gt geq ite ite_set mk_and_sp mk_and mk_or mk_union mk_intersection mk_sing is_subset is_member vint cint vbool vset cemptyset cunivset sf =
    let
        all_coeffs = sy_coeffs sf
        lin_ineqs = map (\(cl_act, cl) -> vbool cl_act:map toLinInEqs cl) all_coeffs
    in
    mk_and_sp . map mk_or $ lin_ineqs
    where
        int_args = map smt_var (int_sy_args_and_ret sf)
        set_args = map smt_var (set_sy_args_and_ret sf)
        bool_args = map smt_var (bool_sy_args_and_ret sf)

        toLinInEqs (LIA { c_active = act
                        , c_op_branch1 = op_br1
                        , c_op_branch2 = op_br2
                        , b0 = b
                        , ars_coeffs = acs
                        , rets_coeffs =  rcs }) =
            let
                sm = lia_form acs rcs
            in
            mk_and [vbool act, ite (vbool op_br1)
                                  (sm `eq` vint b)
                                  (ite (vbool op_br2) (sm `gt` vint b)
                                               (sm `geq` vint b)
                                  )
                   ]
        toLinInEqs (Set { c_active = act
                        , c_op_branch1 = op_br1
                        , c_op_branch2 = op_br2 

                        , int_sing_set_bools_lhs = int_sing_bools_lhs
                        , int_sing_set_bools_rhs = int_sing_bools_rhs

                        , ars_bools_lhs = ars_b1
                        , rets_bools_lhs = rets_b1
                        , ars_bools_rhs = ars_b2
                        , rets_bools_rhs = rets_b2 }) =
            let
                sm1 = set_form ars_b1 rets_b1 int_sing_bools_lhs
                sm2 = set_form ars_b2 rets_b2 int_sing_bools_rhs
            in
            mk_and [vbool act, sm1 `eq` sm2]
        toLinInEqs (BoolForm { c_active = act
                             , ars_bools = as
                             , rets_bools = rs
                             , forms = frms }) =
            let
                bb = zipWith (\x y -> mk_or [x, y]) (map vbool $ as ++ rs) (map vbool bool_args)
            in
            mk_and [vbool act, mk_and bb `eq_bool` mk_and (map toLinInEqs frms)]

        lia_form acs rcs = foldr plus (cint 0)
                         . map (uncurry mult)
                         $ zip (map vint $ acs ++ rcs) (map vint int_args)

        set_form ars rts is_bools =
            let
                sets = map vset set_args
                ars_rts = map (map vbool) $ zipWith (++) ars rts

                ite_sets = map (zipWith (\s a -> ite_set a s cunivset) sets) ars_rts
               
                ints = map vint int_args
                ite_sing_sets = map (:[]) $ map (foldr (\(i, b) -> ite_set (vbool b) (mk_sing i)) cunivset . zip ints) is_bools -- map (zipWith (\s a -> ite_set (vbool a) (mk_sing s) cunivset) ints) is_bools
               
                ite_sets' = if not (null ite_sing_sets)
                                then zipWith (++) ite_sets ite_sing_sets
                                else ite_sets
            in
            if not (null ite_sets') && any (not . null) ite_sets'
                then foldr1 mk_union
                        . map (foldr1 mk_intersection)
                        $ ite_sets'
                else cemptyset
            -- foldr mk_union cemptyset
            --        . map (\(b, s) -> ite_set b s cemptyset)
            --        $ zip (map vbool $ ars ++ rts) (map vset set_args)


----------------------------------------------------------------------------
-- Polymorphic access measures
-- A measure is a polymorphic access measure if it returns a value of a polymorphic type.
-- For example, `fst :: (a, b) -> a`.
-- Specifications that use both tuple style specs i.e. ( {x:Int > 0 }, Int)
-- and measure style specs i.e. { t:(Int, Int) | fst t > 0 } together can cause strange
-- errors from LH.  Thus, we add softer assertions to, when possible,
-- avoid using polymorphic access measures.

polyAccessConstraints2 :: [GhcInfo] -> Measures -> M.Map Name SpecInfo -> [SMTHeader]
polyAccessConstraints2 ghci meas =
    let
      pa_meas = getPolyAccessMeasures ghci meas
    in
      map (flip AssertSoft Nothing)
    . polyAccessConstraints2' pa_meas
    . M.filter (\si -> s_status si == Synth)

polyAccessConstraints2' :: [(LH.Symbol, Type, Type)] -> M.Map Name SpecInfo -> [SMTAST]
polyAccessConstraints2' meas = concatMap (polyAccessConstraints2'' meas) . M.elems

polyAccessConstraints2'' :: [(LH.Symbol, Type, Type)] -> SpecInfo -> [SMTAST]
polyAccessConstraints2'' meas si =
    let
        poly = allSynthSpecPoly si
    in
    concatMap (polyAccessConstraints2''' meas) $ concatMap extractValues poly

polyAccessConstraints2''' :: [(LH.Symbol, Type, Type)] -> SynthSpec -> [SMTAST]
polyAccessConstraints2''' meas sys =
    let
        cffs = sySpecGetCoeffsNoB sys
        ars_cffs =
              if not (null (sy_args sys)) || not (null (sy_rets sys))
                  then zip (cycle (sy_args sys ++ sy_rets sys)) cffs
                  else []
    in
    concatMap (\(sy, c) -> if usesPolyAcc (lh_rep sy)
                              then [V c SortInt := VInt 0]
                              else []) ars_cffs
    where
      meas' = map (\(m, _, _) -> m) meas

      usesPolyAcc (EApp (EVar lh) e) = lh `elem` meas' || usesPolyAcc e
      usesPolyAcc _ = False

getPolyAccessMeasures :: [GhcInfo] -> Measures -> [(LH.Symbol, Type, Type)]
getPolyAccessMeasures ghci =
      map (\(n, at, rt) -> (getLHMeasureName ghci n, at, rt)) 
    . mapMaybe (\(n, (t:ts, rt)) -> if null ts then Just (n, t, rt) else Nothing)
    . HM.toList
    . E.map' (\e -> (filter (not . isLHDict) $ anonArgumentTypes e, returnType e))
    . E.filter (isTyVar . returnType)
    where
        isLHDict t
          | (TyCon (Name n _ _ _) _):_ <- unTyApp t = n == "lh"
          | otherwise = False

----------------------------------------------------------------------------

-- Helpers for SynthInfo
allSynthSpec :: SpecInfo -> [SynthSpec]
allSynthSpec si = allPreSynthSpec si ++ allPostSynthSpec si

allPreSynthSpec :: SpecInfo -> [SynthSpec]
allPreSynthSpec = concatMap extractValues . s_syn_pre

allPostSynthSpec :: SpecInfo -> [SynthSpec]
allPostSynthSpec = extractValues . s_syn_post

allSynthSpecPoly :: SpecInfo -> [PolyBound SynthSpec]
allSynthSpecPoly si = s_syn_pre si ++ [s_syn_post si]

allCNFs :: SpecInfo -> CNF
allCNFs si = allPreCoeffs si ++ allPostCoeffs si

allPreCoeffs :: SpecInfo -> CNF
allPreCoeffs = concatMap sy_coeffs . allPreSynthSpec

allPostCoeffs :: SpecInfo -> CNF
allPostCoeffs = concatMap sy_coeffs . allPostSynthSpec

allPostSpecArgs :: SpecInfo -> [SpecArg]
allPostSpecArgs = concatMap sy_args_and_ret . allPostSynthSpec

allCNFsSeparated :: SpecInfo -> [CNF]
allCNFsSeparated si = allPreCoeffsSeparated si ++ allPostCoeffsSeparated si

allPreCoeffsSeparated :: SpecInfo -> [CNF]
allPreCoeffsSeparated = map sy_coeffs . allPreSynthSpec

allPostCoeffsSeparated :: SpecInfo -> [CNF]
allPostCoeffsSeparated = map sy_coeffs . allPostSynthSpec

allForms :: SpecInfo -> [Forms]
allForms = concatMap allFormsFromForm
         . concatMap snd
         . allCNFs

allFormsFromForm :: Forms -> [Forms]
allFormsFromForm frm@(BoolForm { forms = frms }) = frm:concatMap allFormsFromForm frms
allFormsFromForm frm = [frm]