{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.Sygus.FCConverter ( NMExprEnv
                                             , convertConstraints) where

import G2.Language as G2
import G2.Liquid.Types
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.FuncConstraint
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.PolyRef
import G2.Liquid.Inference.Sygus.SpecInfo

import qualified Data.HashMap.Lazy as HM
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

type ConvertExpr a = G2.Expr -> a
type AndF a = [a] -> a
type OrF a = [a] -> a
type NotF a = a -> a
type ImpliesF a = a -> a -> a

type Func a = String -> [a] -> a
type KnownFunc a = String -> Integer -> Bool -> a
type ToBeFunc a = String -> Integer -> Bool -> a

------------------------------------
-- Building Formulas
------------------------------------

mkPreCall :: ProgresserM m => 
             ConvertExpr form
          -> AndF form
          -> OrF form
          -> Func form
          -> KnownFunc form
          -> ToBeFunc form
          -> NMExprEnv 
          -> TypeEnv 
          -> Measures
          -> MeasureExs
          -> Evals (Integer, Bool)
          -> M.Map Name SpecInfo
          -> FuncCall
          -> m form
mkPreCall convExpr andF orF funcF knownF toBeF eenv tenv meas meas_ex evals m_si fc@(FuncCall { funcName = n, arguments = ars })
    | Just si <- M.lookup n m_si
    , Just (ev_i, ev_b) <- lookupEvals fc (pre_evals evals)
    , Just func_e <- HM.lookup (nameOcc n, nameModule n) eenv = do
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
                            smt_ars = concat $ map (uncurry (adjustArgs convExpr (fromInteger mx_meas) tenv meas meas_ex)) t_ars

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
                                    smt_r = map (adjustArgs convExpr (fromInteger mx_meas) tenv meas meas_ex rt) re
                                in
                                map (\r -> funcF (sy_name psi) $ smt_ars ++ r) smt_r
                              ) $ extractValues si_re_rt_pb
                  ) . zip (s_syn_pre si) . filter (not . null) $ L.inits v_ars

            sy_body = andF sy_body_p
            fixed_body = knownF (s_known_pre_name si) ev_i ev_b
            to_be_body = toBeF (s_to_be_pre_name si) ev_i ev_b

        case s_status si of
                Synth -> return $ andF [fixed_body, sy_body]
                ToBeSynthed -> return $ andF [fixed_body, to_be_body]
                Known -> return $ fixed_body
    | otherwise = error "mkPreCall: specification not found"

mkPostCall :: ProgresserM m => 
              ConvertExpr form
           -> AndF form
           -> OrF form
           -> Func form
           -> KnownFunc form
           -> ToBeFunc form
           -> NMExprEnv
           -> TypeEnv
           -> Measures
           -> MeasureExs
           -> Evals (Integer, Bool)
           -> M.Map Name SpecInfo
           -> FuncCall
           -> m form
mkPostCall convExpr andF orF funcF knownF toBeF eenv tenv meas meas_ex evals m_si fc@(FuncCall { funcName = n, arguments = ars, returns = r })
    | Just si <- M.lookup n m_si
    , Just (ev_i, ev_b) <- lookupEvals fc (post_evals evals)
    , Just func_e <- HM.lookup (nameOcc n, nameModule n) eenv = do
        MaxSize mx_meas <- maxSynthSizeM
        let func_ts = argumentTypes func_e

            smt_ars = concatMap (uncurry (adjustArgs convExpr (fromInteger mx_meas) tenv meas meas_ex))
                    . filter (\(t, _) -> not (isTyFun t) && not (isTyVar t))
                    . filter (validArgForSMT . snd) $ zip func_ts ars
            
            smt_ret = extractExprPolyBoundWithRoot r
            smt_ret_ty = extractTypePolyBound (returnType func_e)
            smt_ret_e_ty = case filterPBByType snd $ zipPB smt_ret smt_ret_ty of
                              Just smt_ret_e_ty' -> smt_ret_e_ty'
                              Nothing -> PolyBound ([], headValue smt_ret_ty) []

            sy_body = andF
                    . concatMap
                        (\(syn_p, r, rt) ->
                            let
                                smt_r = map (adjustArgs convExpr (fromInteger mx_meas) tenv meas meas_ex rt) $ r
                            in
                            map (\smt_r' -> funcF (sy_name syn_p) $ smt_ars ++ smt_r') smt_r)
                    . extractValues 
                    $ zipWithPB (\x (y, z) -> (x, y, z)) (s_syn_post si) smt_ret_e_ty
            fixed_body = knownF (s_known_post_name si) ev_i ev_b
            to_be_body = toBeF (s_to_be_post_name si) ev_i ev_b

        case s_status si of
                Synth -> return $ andF [fixed_body, sy_body]
                ToBeSynthed -> return $ andF [fixed_body, to_be_body]
                Known -> return $ fixed_body
    | otherwise = error "mkPostCall: specification not found"

convertConstraints :: (InfConfigM m, ProgresserM m) =>
                      ConvertExpr form
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
convertConstraints convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si fc = do
    let fc' = toListFC fc
    mapM (convertConstraint 
                    convExpr
                    andF
                    orF
                    notF
                    impF
                    funcF
                    knownF
                    toBeF
                    eenv tenv meas meas_ex evals si) fc'

convertConstraint :: (InfConfigM m, ProgresserM m) =>
                     ConvertExpr form
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
convertConstraint convExpr andF orF _ impF funcF knownF toBeF eenv tenv meas meas_ex evals si (Call All fc) = do
    pre <- mkPreCall convExpr andF orF funcF knownF toBeF eenv tenv meas meas_ex evals si fc
    post <- mkPostCall convExpr andF orF funcF knownF toBeF eenv tenv meas meas_ex evals si fc
    return $ pre `impF` post
convertConstraint convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si (Call Pre fc) =
    mkPreCall convExpr andF orF funcF knownF toBeF eenv tenv meas meas_ex evals si fc
convertConstraint convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si (Call Post fc) =
    mkPostCall convExpr andF orF funcF knownF toBeF eenv tenv meas meas_ex evals si fc
convertConstraint convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si (AndFC fs) =
    return . andF =<< mapM (convertConstraint convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si) fs
convertConstraint convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si (OrFC fs) =
    return . orF =<< mapM (convertConstraint convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si) fs
convertConstraint convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si (ImpliesFC fc1 fc2) = do
    lhs <- convertConstraint convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si fc1
    rhs <- convertConstraint convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si fc2
    return $ lhs `impF` rhs
convertConstraint convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si (NotFC fc) =
    return . notF =<< convertConstraint convExpr andF orF notF impF funcF knownF toBeF eenv tenv meas meas_ex evals si fc

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
