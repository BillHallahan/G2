{-# LANGUAGE TupleSections #-}

module G2.Liquid.Inference.Sygus.CheckAbstractFC (genCounterexampleFromAbstractFC) where

import G2.Language
import qualified G2.Language.PathConds as PC
import G2.Solver as Solver

import G2.Liquid.Types
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.FuncConstraint
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.Sygus.FCConverter
import G2.Liquid.Inference.Sygus.SpecInfo

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.Map as M

import qualified Text.Builder as TB

genCounterexampleFromAbstractFC :: (InfConfigM m, ProgresserM m) =>
                                   NMExprEnv -> TypeEnv -> Measures -> MeasureExs -> Evals (Integer, Bool) -> M.Map Name SpecInfo -> FuncConstraint -> m (Maybe [SMTHeader])
genCounterexampleFromAbstractFC eenv tenv meas meas_ex evals m_si fc = do
    let all_calls = map abs_fcall $ allCalls fc
        all_symbs = HS.map nameToStr . HS.map idName . HS.filter (isPrimType . typeOf) . HS.unions . map symb_fc $ all_calls
        
        all_pc = foldr PC.union PC.empty $ map paths_fc all_calls
        expr_pc = mkSMTAnd . map pathConsToSMT $ PC.toList all_pc

        var_decls = map (flip VarDecl SortInt . TB.string) $ HS.toList all_symbs

    abs_fc <- constraintToSMT eenv tenv meas meas_ex evals m_si fc

    case null all_symbs of
        True -> return Nothing
        False -> return $ Just (var_decls ++ [Solver.Assert $ expr_pc :=> abs_fc])

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
                    (\n _ _ -> Func n [VInt 0])
                    eenv tenv meas meas_ex evals si fc
    where
        ifNotNull _ def [] = def
        ifNotNull f _ xs = f xs

