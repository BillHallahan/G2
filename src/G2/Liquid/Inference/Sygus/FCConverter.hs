{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.Sygus.FCConverter ( NMExprEnv
                                             , convertConstraints
                                             , convertConstraint
                                             , constraintsToSMT
                                             , convertExprToSMT
                                             , falseArray
                                             , trueArray) where

import G2.Language as G2
import qualified G2.Language.PathConds as PC
import G2.Liquid.Types
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.FuncConstraint
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.PolyRef
import G2.Liquid.Inference.Sygus.SpecInfo
import G2.Solver as Solver

import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

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
                    pathConsToSMT
                    (\is -> Forall (map (\n -> (n, SortInt)) is))
                    (ifNotNull mkSMTAnd (VBool True))
                    (ifNotNull mkSMTOr (VBool False))
                    (:!)
                    (:=>)
                    Func
                    (\n i _ _ -> Func n [VInt i])
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

trueArray :: SMTAST
trueArray = V "true_array" (SortArray SortInt SortBool)

falseArray :: SMTAST
falseArray = V "false_array" (SortArray SortInt SortBool)


type ConvertExpr a = G2.Expr -> a
type ConvertPC a = PC.PathCond -> a
type ForallF a = [String] -> a -> a
type AndF a = [a] -> a
type OrF a = [a] -> a
type NotF a = a -> a
type ImpliesF a = a -> a -> a

type Func a = String -> [a] -> a
type KnownFunc a = String -> Integer -> Bool -> a -> a
type ToBeFunc a = String -> Integer -> Bool -> a

------------------------------------
-- Building Formulas
------------------------------------

mkPreCall :: (InfConfigM m, ProgresserM m) => 
             (ConcAbsFuncCall -> FuncCall)
          -> ConvertExpr form
          -> AndF form
          -> Func form
          -> KnownFunc form
          -> ToBeFunc form
          -> NMExprEnv 
          -> TypeEnv 
          -> Measures
          -> MeasureExs
          -> Evals (Integer, Bool)
          -> M.Map Name SpecInfo
          -> ConcAbsFuncCall
          -> m form
mkPreCall extract_fc convExpr andF funcF knownF toBeF eenv tenv meas meas_ex evals m_si ca_fc
    | fc@(FuncCall { funcName = n, arguments = ars }) <- extract_fc ca_fc
    , Just si <- M.lookup n m_si
    , Just func_e <- HM.lookup (nameOcc n, nameModule n) eenv = do
        inf_config <- infConfigM

        MaxSize mx_meas <- maxSynthSizeM
        let func_ts = argumentTypes func_e

            v_ars = filter (validArgForSMT . snd)
                  . filter (\(t, _) -> not (isTyFun t) && not (isTyVar t))
                  $ zip func_ts ars

            sy_body_p =
                concatMap
                    (\(si_pb, ts_es) ->
                        let
                            t_ars = init ts_es
                            smt_ars = concat $ map (uncurry (adjustArgsWithCare inf_config n convExpr (fromInteger mx_meas) tenv meas meas_ex)) t_ars

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
                                    f_smt_ars = if null (sy_args psi) then [] else smt_ars
                                    smt_r = map (adjustArgs convExpr (fromInteger mx_meas) tenv meas meas_ex rt) re
                                in
                                map (\r -> funcF (sy_name psi) $ f_smt_ars ++ r) smt_r
                              ) $ extractValues si_re_rt_pb
                  ) . zip (s_syn_pre si) . filter (not . null) $ L.inits v_ars

            (ev_i, ev_b) = case lookupEvals fc (pre_evals evals) of
                                  Just ev -> ev
                                  Nothing -> error "mkPreCall: Missing eval"
            sy_body = andF sy_body_p
            fixed_body = knownF (s_known_pre_name si) ev_i ev_b sy_body
            to_be_body = toBeF (s_to_be_pre_name si) ev_i ev_b

        case s_status si of
                Synth -> return $ andF [fixed_body, sy_body]
                ToBeSynthed -> return $ andF [fixed_body, to_be_body]
                Known -> return $ fixed_body
    | otherwise = error $ "mkPreCall: specification not found" ++ show (ca_fc) ++ "\n" ++ show (M.keys m_si)

mkPostCall :: (InfConfigM m, ProgresserM m) => 
              (ConcAbsFuncCall -> FuncCall) 
           -> ConvertExpr form
           -> AndF form
           -> Func form
           -> KnownFunc form
           -> ToBeFunc form
           -> NMExprEnv 
           -> TypeEnv 
           -> Measures
           -> MeasureExs
           -> Evals (Integer, Bool)
           -> M.Map Name SpecInfo
           -> ConcAbsFuncCall
           -> m form
mkPostCall extract_fc convExpr andF funcF knownF toBeF eenv tenv meas meas_ex evals m_si ca_fc
    | fc@(FuncCall { funcName = n, arguments = ars, returns = r }) <- extract_fc ca_fc
    , Just si <- M.lookup n m_si
    , Just func_e <- HM.lookup (nameOcc n, nameModule n) eenv = do
        inf_config <- infConfigM

        MaxSize mx_meas <- maxSynthSizeM
        let func_ts = argumentTypes func_e

            smt_ars = concatMap (uncurry (adjustArgsWithCare inf_config n convExpr (fromInteger mx_meas) tenv meas meas_ex))
                    . filter (\(t, _) -> not (isTyFun t) && not (isTyVar t))
                    . filter (validArgForSMT . snd) $ zip func_ts ars

            smt_ret = extractExprPolyBoundWithRoot r
            smt_ret_ty = extractTypePolyBound (returnType func_e)
            smt_ret_e_ty = case filterPBByType snd $ zipPB smt_ret smt_ret_ty of
                              Just smt_ret_e_ty' -> smt_ret_e_ty'
                              Nothing -> PolyBound ([], headValue smt_ret_ty) []

            (ev_i, ev_b) = case lookupEvals fc (post_evals evals) of
                                  Just ev -> ev
                                  Nothing -> error "mkPostCall: Missing eval"

            sy_body = andF
                    . concatMap
                        (\(syn_p, r, rt) ->
                            let
                                f_smt_ars = if null (sy_args syn_p) then [] else smt_ars
                                smt_r = map (adjustArgs convExpr (fromInteger mx_meas) tenv meas meas_ex rt) $ r
                            in
                            map (\smt_r' -> funcF (sy_name syn_p) $ f_smt_ars ++ smt_r') smt_r)
                    . extractValues 
                    $ zipWithPB (\x (y, z) -> (x, y, z)) (s_syn_post si) smt_ret_e_ty
            fixed_body = knownF (s_known_post_name si) ev_i ev_b sy_body
            to_be_body = toBeF (s_to_be_post_name si) ev_i ev_b

        case s_status si of
                Synth -> return $ andF [fixed_body, sy_body]
                ToBeSynthed -> return $ andF [fixed_body, to_be_body]
                Known -> return $ fixed_body
    | otherwise = error "mkPostCall: specification not found"

convertConstraints :: (InfConfigM m, ProgresserM m) =>
                      ConvertExpr form
                   -> ConvertPC form
                   -> ForallF form
                   -> AndF form
                   -> OrF form
                   -> NotF form
                   -> ImpliesF form
                   -> Func form
                   -> KnownFunc form
                   -> ToBeFunc form
                   -> NMExprEnv
                   -> TypeEnv
                   -> Measures
                   -> MeasureExs
                   -> Evals (Integer, Bool)
                   -> M.Map Name SpecInfo
                   -> FuncConstraints
                   -> m [form]
convertConstraints convExpr convPC forallF andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si fc = do
    let fc' = toListFC fc
    mapM (convertConstraint 
                    conc_fcall
                    convExpr
                    convPC
                    forallF
                    andF
                    orF
                    notF
                    impF
                    funcF
                    knownF
                    toBeF
                    eenv tenv meas meas_ex evals si) fc'

convertConstraint :: (InfConfigM m, ProgresserM m) =>
                     (ConcAbsFuncCall -> FuncCall)
                  -> ConvertExpr form
                  -> ConvertPC form
                  -> ForallF form
                  -> AndF form
                  -> OrF form
                  -> NotF form
                  -> ImpliesF form
                  -> Func form
                  -> KnownFunc form
                  -> ToBeFunc form
                  -> NMExprEnv
                  -> TypeEnv
                  -> Measures
                  -> MeasureExs
                  -> Evals (Integer, Bool)
                  -> M.Map Name SpecInfo
                  -> FuncConstraint
                  -> m form
convertConstraint extract_fc convExpr convPC forallF andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si constraint =
    let
        -- all_calls = allCalls constraint
        -- all_symbs = HS.map nameToStr . HS.map idName . HS.filter (isPrimType . typeOf) . HS.unions . map symb_fc $ all_calls
        
        -- all_pc = foldr PC.union PC.empty $ map paths_fc all_calls
        -- expr_pc = andF . map convPC $ PC.toList all_pc

        con_constraint = convertConstraint' extract_fc convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si constraint
    in
    con_constraint
    -- case null all_symbs of
    --     True -> con_constraint
    --     False -> return . forallF (HS.toList all_symbs) . impF expr_pc =<< con_constraint

convertConstraint' :: (InfConfigM m, ProgresserM m) =>
                      (ConcAbsFuncCall -> FuncCall)
                   -> ConvertExpr form
                   -> AndF form
                   -> OrF form
                   -> NotF form
                   -> ImpliesF form
                   -> Func form
                   -> KnownFunc form
                   -> ToBeFunc form
                   -> NMExprEnv
                   -> TypeEnv
                   -> Measures
                   -> MeasureExs
                   -> Evals (Integer, Bool)
                   -> M.Map Name SpecInfo
                   -> FuncConstraint
                   -> m form
convertConstraint' extract_fc convExpr andF orF _ impF funcF knownF toBeF eenv tenv meas meas_ex evals si (Call All fc) = do
    pre <- mkPreCall extract_fc convExpr andF funcF knownF toBeF eenv tenv meas meas_ex evals si fc
    post <- mkPostCall extract_fc convExpr andF funcF knownF toBeF eenv tenv meas meas_ex evals si fc
    return $ pre `impF` post
convertConstraint' extract_fc convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si (Call Pre fc) =
    mkPreCall extract_fc convExpr andF funcF knownF toBeF eenv tenv meas meas_ex evals si fc
convertConstraint' extract_fc convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si (Call Post fc) =
    mkPostCall extract_fc convExpr andF funcF knownF toBeF eenv tenv meas meas_ex evals si fc
convertConstraint' extract_fc convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si (AndFC fs) =
    return . andF =<< mapM (convertConstraint' extract_fc convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si) fs
convertConstraint' extract_fc convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si (OrFC fs) =
    return . orF =<< mapM (convertConstraint' extract_fc convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si) fs
convertConstraint' extract_fc convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si (ImpliesFC fc1 fc2) = do
    lhs <- convertConstraint' extract_fc convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si fc1
    rhs <- convertConstraint' extract_fc convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si fc2
    return $ lhs `impF` rhs
convertConstraint' extract_fc convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si (NotFC fc) =
    return . notF =<< convertConstraint' extract_fc convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si fc

adjustArgs :: ConvertExpr form -> Int -> TypeEnv -> Measures -> MeasureExs -> Type -> G2.Expr -> [form]
adjustArgs convExpr mx_meas tenv meas meas_ex t =
      map convExpr
    . map adjustLits
    . substMeasures mx_meas tenv meas meas_ex t

substMeasures :: Int -> TypeEnv -> Measures -> MeasureExs -> Type -> G2.Expr -> [G2.Expr]
substMeasures mx_meas tenv meas meas_ex t e =
    case typeToSort t of
        Just _ -> [e]
        Nothing ->
            case HM.lookup e meas_ex of
                Just es ->
                    let
                        -- Get a list of all measure/output pairs with usable types
                        es' = filter (isJust . typeToSort . returnType . snd) $ HM.toList es
                        -- Make sure that es's type is specific enough to be used with the measure
                        app_meas = applicableMeasures mx_meas tenv meas t
                        es'' = filter (\(ns, _) -> ns `HM.member` app_meas) es'
                    in
                    -- Sort to make sure we get the same order consistently
                    map snd $ L.sortBy (\(n1, _) (n2, _) -> compare n1 n2) es''
                Nothing -> []

adjustArgsWithCare :: InferenceConfig -> Name -> ConvertExpr form -> Int -> TypeEnv -> Measures -> MeasureExs -> Type -> G2.Expr -> [form]
adjustArgsWithCare inf_config n convExpr mx_meas tenv meas meas_ex t
    | use_invs inf_config
    , specialFunction n =
          map convExpr
        . map adjustLits
        . (\e -> case typeToSort t of Just _ -> [e]; Nothing -> [])
    | otherwise = adjustArgs convExpr mx_meas tenv meas meas_ex t

adjustLits :: G2.Expr -> G2.Expr
adjustLits (App _ e) | isPrimType (typeOf e) = e
adjustLits e = e

validArgForSMT :: G2.Expr -> Bool
validArgForSMT e = not (isLHDict e) && not (isType e)
    where
        isType (Type _) = True
        isType _ = False

        isLHDict e
            | (TyCon (Name n _ _ _) _):_ <- unTyApp (typeOf e) = n == "lh"
            | otherwise = False
