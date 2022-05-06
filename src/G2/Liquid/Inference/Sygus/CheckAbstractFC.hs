{-# LANGUAGE TupleSections #-}

module G2.Liquid.Inference.Sygus.CheckAbstractFC (genCounterexampleFromAbstractFC) where

import G2.Execution.PrimitiveEval
import G2.Language
import qualified G2.Language.PathConds as PC
import G2.Solver as Solver

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

import Language.Haskell.Liquid.Types
import Language.Fixpoint.Types.Refinements as LH hiding (pAnd, pOr)

import Control.Monad.IO.Class 

import Data.Function
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import qualified Data.Map as M

import qualified Text.Builder as TB

genCounterexampleFromAbstractFC :: (MonadIO m, InfConfigM m, ProgresserM m, SMTConverter con ast out io) =>
                                   con
                                -> [GhcInfo]
                                -> NMExprEnv
                                -> TypeEnv
                                -> Measures
                                -> MeasureExs
                                -> Evals (Integer, Bool)
                                -> M.Map Name SpecInfo
                                -> GeneratedSpecs
                                -> FuncConstraint
                                -> m (Maybe FuncConstraint)
genCounterexampleFromAbstractFC con ghci eenv tenv meas meas_ex evals m_si gs fc = do
    m_form_vs <- genCounterexampleFormula ghci eenv tenv meas meas_ex evals m_si gs fc
    case m_form_vs of
        Just (form, vs) -> do
            mdl <- liftIO $ solveConstraints con form vs
            return $ fmap (foldr (uncurry replaceVar) (switchAbsFC fc) . HM.toList) mdl
        Nothing -> return Nothing

genCounterexampleFormula :: (MonadIO m, InfConfigM m, ProgresserM m) =>
                            [GhcInfo]
                         -> NMExprEnv
                         -> TypeEnv
                         -> Measures
                         -> MeasureExs
                         -> Evals (Integer, Bool)
                         -> M.Map Name SpecInfo
                         -> GeneratedSpecs
                         -> FuncConstraint
                         -> m (Maybe ([SMTHeader], [(SMTName, Sort)]))
genCounterexampleFormula ghci eenv tenv meas meas_ex evals m_si gs fc = do
    let all_calls = map abs_fcall $ allCalls fc
        all_symbs = HS.map nameToStr . HS.map idName . HS.filter (isPrimType . typeOf) . HS.unions . map symb_fc $ all_calls
        
        all_pc = foldr PC.union PC.empty $ map paths_fc all_calls
        expr_pc = case PC.toList all_pc of
                        [] -> []
                        pc_list -> [Solver.Assert . mkSMTAnd $ map pathConsToSMT pc_list]

        var_decls = map (flip VarDecl SortInt . TB.string) . nub $ HS.toList all_symbs

        func_defs = concatMap (funcDefToSMTAST ghci m_si gs) . nub $ map (funcName . fcall) all_calls

    case not (null all_symbs) && all (flip memberAssertGS gs . funcName . fcall) all_calls of
        False -> return Nothing
        True -> do
            abs_fc <- constraintToSMT eenv tenv meas meas_ex evals m_si fc
            return $ Just (var_decls ++ func_defs ++ expr_pc ++ [Solver.Assert $ (:!) abs_fc], zip (HS.toList all_symbs) (repeat SortInt))

constraintToSMT :: (InfConfigM m, ProgresserM m) =>
                   NMExprEnv
                -> TypeEnv
                -> Measures
                -> MeasureExs
                -> Evals (Integer, Bool)
                -> M.Map Name SpecInfo
                -> FuncConstraint
                -> m SMTAST
constraintToSMT eenv tenv meas meas_ex evals si fc =
        convertConstraint
                    (fcall . abs_fcall)
                    convertExprToSMT
                    pathConsToSMT
                    (\is -> Forall (map (\n -> (n, SortInt)) is))
                    (ifNotNull mkSMTAnd (VBool True))
                    (ifNotNull mkSMTOr (VBool False))
                    (:!)
                    (:=>)
                    Func
                    (\n _ _ -> id)
                    -- We cannot use an abstract FuncConstraint involving a function f with an unknown specification
                    -- to generate counterexamples.  Suppose we are synthesizing at level N. f must be at a level > N.
                    -- Then, we will generate a constraint that will not have to be satsified until a level > N,
                    -- and we will repeatedly generate that constraint at every `genCounterexampleFromAbstractFC`
                    -- check, resulting in an infinite loop.
                    (error "constraintToSMT: use of unknown function specification")
                    eenv tenv meas meas_ex evals si fc
    where
        ifNotNull _ def [] = def
        ifNotNull f _ xs = f xs

funcDefToSMTAST :: [GhcInfo] -> M.Map Name SpecInfo -> GeneratedSpecs -> Name -> [SMTHeader]
funcDefToSMTAST ghci m_si gs n | Just si <- f_si =
                                let
                                    si_ars = s_syn_pre si
                                    si_ret = s_syn_post si

                                    spec = case lookupAssertGS n gs of
                                                Just spc -> spc
                                                Nothing -> replicate (length si_ars + 1) (PolyBound PTrue [])

                                    ghci_spec = existingPBExpr n ghci
                                    full_spec = maybe spec (merge_specs spec) ghci_spec

                                    spec_ars = init full_spec
                                    spec_ret = last full_spec
                                in
                                concatMap (uncurry funcDefToSMTAST') . nubBy ((==) `on` sy_name . headValue . fst) $ (si_ret, spec_ret):zip si_ars spec_ars
                               | otherwise = error "funcDefToSMTAST: function not found"
    where
        f_si = M.lookup (zeroOutName n) m_si
        zeroOutName (Name n m _ l) = Name n m 0 l

        merge_specs spc = map (uncurry (zipWithMaybePB (\s1 s2 -> PAnd [maybe PTrue id s1, maybe PTrue id s2]))) . zip spc

funcDefToSMTAST' :: PolyBound SynthSpec -> PolyBound LH.Expr -> [SMTHeader]
funcDefToSMTAST' pb_sy_s = map (uncurry funcDefToSMTAST'') . extractValues . zipWithMaybePB merge pb_sy_s
    where
        merge (Just s) (Just e) = (s, e) 
        merge (Just s) Nothing = (s, PTrue)
        merge Nothing _ = error "funcDefToSMTAST': missing SynthSpec" 

funcDefToSMTAST'' :: SynthSpec -> LH.Expr -> SMTHeader
funcDefToSMTAST'' synth_spec e =
    let
        ars = sy_args synth_spec ++ sy_rets synth_spec
        body = lhExprToSMT ars e
    in
    DefineFun (sy_name synth_spec) (map (\sa -> (smt_var sa, smt_sort sa)) ars) SortBool body

lhExprToSMT :: [SpecArg] -> LH.Expr -> SMTAST
lhExprToSMT spec_args evar@(EVar _) | Just sa <- find (\sa_ -> lh_rep sa_ == evar) spec_args = V (smt_var sa) (smt_sort sa)
lhExprToSMT spec_args evar@(EApp _ _) | Just sa <- find (\sa_ -> lh_rep sa_ == evar) spec_args = V (smt_var sa) (smt_sort sa)
lhExprToSMT _ (ECon (I i)) = VInt i
lhExprToSMT spec_args (ENeg x) = Neg $ lhExprToSMT spec_args x
lhExprToSMT spec_args (EBin LH.Plus x y) = lhExprToSMT spec_args x :+ lhExprToSMT spec_args y
lhExprToSMT spec_args (EBin LH.Times x y) = lhExprToSMT spec_args x :* lhExprToSMT spec_args y
lhExprToSMT spec_args (EIte b x y) =
    (lhExprToSMT spec_args b :=> lhExprToSMT spec_args x) .&&. (((:!) (lhExprToSMT spec_args b)) :=> lhExprToSMT spec_args y)
lhExprToSMT spec_args (PAtom LH.Gt x y) = lhExprToSMT spec_args x :> lhExprToSMT spec_args y
lhExprToSMT spec_args (PAtom LH.Ge x y) = lhExprToSMT spec_args x :>= lhExprToSMT spec_args y
lhExprToSMT spec_args (PAtom LH.Eq x y) = lhExprToSMT spec_args x := lhExprToSMT spec_args y
lhExprToSMT spec_args PTrue = VBool True
lhExprToSMT spec_args PFalse = VBool False
lhExprToSMT spec_args (PAnd xs) = mkSMTAnd $ map (lhExprToSMT spec_args) xs 
lhExprToSMT spec_args (POr xs) = mkSMTOr $ map (lhExprToSMT spec_args) xs
lhExprToSMT spec_args (PIff x y) = lhExprToSMT spec_args x :<=> lhExprToSMT spec_args y
lhExprToSMT _ e = error $ "lhExprToSMT: Unhandled expr " ++ show e

existingPBExpr :: Name -> [GhcInfo] -> Maybe [PolyBound LH.Expr]
existingPBExpr n = fmap lhSpecToPolyBoundExpr . findLHSpec n

findLHSpec :: Name -> [GhcInfo] -> Maybe SpecType
findLHSpec n = fmap val . fmap snd . find (flip varEqName n . fst) . concatMap getTySigs

lhSpecToPolyBoundExpr :: SpecType -> [PolyBound LH.Expr]
lhSpecToPolyBoundExpr (RFun { rt_in = i, rt_out = out }) =
    case lhSpecToPolyBoundExpr i of
        [pb_i] -> pb_i:lhSpecToPolyBoundExpr out
        _ -> error "lhSpecToPolyBoundExpr: Unhandled case"
lhSpecToPolyBoundExpr (RAllT { rt_ty = out }) = lhSpecToPolyBoundExpr out
lhSpecToPolyBoundExpr (RApp { rt_reft = u@(MkUReft { ur_reft = Reft (ur_s, ur_e) }), rt_args = ars }) =
    [PolyBound ur_e $ concatMap lhSpecToPolyBoundExpr ars]
lhSpecToPolyBoundExpr e = [PolyBound PTrue [] ]

switchAbsFC :: FuncConstraint -> FuncConstraint
switchAbsFC (Call sp fc) = Call sp (fc { conc_fcall = fcall $ abs_fcall fc })
switchAbsFC (AndFC fs) = AndFC $ map switchAbsFC fs
switchAbsFC (OrFC fs) = OrFC $ map switchAbsFC fs
switchAbsFC (ImpliesFC fc1 fc2) = ImpliesFC (switchAbsFC fc1) (switchAbsFC fc2)
switchAbsFC (NotFC fc) = NotFC (switchAbsFC fc)
