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
import Data.Tuple.Extra

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

mkPreCall :: (InfConfigM m, ProgresserM m) => 
             ConvertExpr form
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
          -> FuncCall
          -> [HigherOrderFuncCall]
          -> m form
mkPreCall convExpr andF funcF knownF toBeF eenv tenv meas meas_ex evals m_si fc@(FuncCall { funcName = n }) hcalls
    | Just si <- M.lookup n m_si
    , Just (ev_i, ev_b) <- lookupEvals fc (pre_evals evals)
    , Just func_e <- HM.lookup (nameOcc n, nameModule n) eenv = do
        sy_body <- mkPreSynthBody convExpr funcF eenv tenv meas meas_ex (s_syn_pre si) (argumentTypes func_e) fc hcalls
        let fixed_body = knownF (s_known_pre_name si) ev_i ev_b
            to_be_body = toBeF (s_to_be_pre_name si) ev_i ev_b

        case s_status si of
                Synth -> return . andF $ fixed_body:sy_body
                ToBeSynthed -> return $ andF [fixed_body, to_be_body]
                Known -> return $ fixed_body
    | otherwise = error "mkPreCall: specification not found"

mkPreSynthBody :: (InfConfigM m, ProgresserM m) => 
                  ConvertExpr form
               -> Func form
               -> NMExprEnv 
               -> TypeEnv 
               -> Measures
               -> MeasureExs
               -> [PolyBound SynthSpec]
               -> [Type]
               -> FuncCall
               -> [HigherOrderFuncCall]
               -> m [form]
mkPreSynthBody convExpr funcF eenv tenv meas meas_ex pre_spec func_ts (FuncCall { funcName = n, arguments = ars }) hcalls = do
        let v_ars = filter (validArgForSMT . thd3)
                  . filter (\(_, t, _) -> not (isTyVar t))
                  . assignNums 1
                  $ zip func_ts ars

        sy_body_p <- mapM (\(si_pb, ts_es) ->
                                let
                                    t_ars = map (\(_, t, e) -> (t, e)) $ init ts_es

                                    (i, l_rt, l_re) = last ts_es
                                    re_pb = extractExprPolyBoundWithRoot l_re
                                    rt_pb = extractTypePolyBound l_rt

                                in
                                case (i, l_rt) of
                                    (Just i', TyFun _ _) -> do -- error $ "HERE\npre_spec = " ++ show pre_spec ++ "\nts_es = " ++ show ts_es
                                        let arg_tys = argumentTypes $ PresType l_rt
                                            return_ty = returnType $ PresType l_rt
                                            hcalls' = filter (\hfc -> nameOcc (funcName hfc) == nameOcc n && nameUnique (funcName hfc) == i') hcalls
                                        clls <- mapM (mkHigherOrderCall convExpr funcF eenv tenv meas meas_ex (removeHead si_pb) arg_tys return_ty) hcalls'
                                        return $ concat clls
                                    _ -> formCalls convExpr funcF tenv meas meas_ex n t_ars si_pb re_pb rt_pb
                          ) . zip pre_spec . filter (not . null) $ L.inits v_ars
        return $ concat sy_body_p
        where
            assignNums _ [] = []
            assignNums i ((t@(TyFun _ _), e):ts) = (Just i, t, e):assignNums (i + 1) ts
            assignNums i  ((t, e):ts) = (Nothing, t, e):assignNums i ts

mkPostCall :: (InfConfigM m, ProgresserM m) => 
              ConvertExpr form
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
           -> FuncCall
           -> m form
mkPostCall convExpr andF funcF knownF toBeF eenv tenv meas meas_ex evals m_si fc@(FuncCall { funcName = n })
    | Just si <- M.lookup n m_si
    , Just (ev_i, ev_b) <- lookupEvals fc (post_evals evals)
    , Just func_e <- HM.lookup (nameOcc n, nameModule n) eenv = do
        let fixed_body = knownF (s_known_post_name si) ev_i ev_b
            to_be_body = toBeF (s_to_be_post_name si) ev_i ev_b

        sy_body <- mkPostSynthBody convExpr funcF tenv meas meas_ex (s_syn_post si) (argumentTypes func_e) (returnType func_e) fc
        case s_status si of
                Synth -> return . andF $ fixed_body:sy_body
                ToBeSynthed -> return $ andF [fixed_body, to_be_body]
                Known -> return $ fixed_body
    | otherwise = error "mkPostCall: specification not found"

mkPostSynthBody :: (InfConfigM m, ProgresserM m) => 
                   ConvertExpr form
                -> Func form
                -> TypeEnv
                -> Measures
                -> MeasureExs
                -> PolyBound SynthSpec
                -> [Type]
                -> Type
                -> FuncCall
                -> m [form]
mkPostSynthBody convExpr funcF tenv meas meas_ex post_spec func_ts ret_ty (FuncCall { funcName = n, arguments = ars, returns = ret }) = do
    let v_ars = filter (\(t, _) -> not (isTyVar t))
              . filter (validArgForSMT . snd)
              $ zip func_ts ars

        smt_ret = extractExprPolyBoundWithRoot ret
        smt_ret_ty = extractTypePolyBound ret_ty

    formCalls convExpr funcF tenv meas meas_ex n v_ars post_spec smt_ret smt_ret_ty

mkHigherOrderCall :: (InfConfigM m, ProgresserM m) =>
                     ConvertExpr form
                  -> Func form
                  -> NMExprEnv
                  -> TypeEnv
                  -> Measures
                  -> MeasureExs
                  -> [PolyBound SynthSpec]
                  -> [Type] -- ^ Argument types
                  -> Type -- ^ Return Type
                  -> FuncCall
                  -> m [form]
mkHigherOrderCall convExpr funcF eenv tenv meas meas_ex pb_synth@(_:_) ar_ts ret_t fc = do
    pre <- mkPreSynthBody convExpr funcF eenv tenv meas meas_ex (init pb_synth) ar_ts fc []
    post <- mkPostSynthBody convExpr funcF tenv meas meas_ex (last pb_synth) ar_ts ret_t fc
    return $ pre ++ post
mkHigherOrderCall _ _ _ _ _ _ _ _ _ _ = return []

formCalls :: (InfConfigM m, ProgresserM m) => ConvertExpr form -> Func form -> TypeEnv -> Measures -> MeasureExs -> Name -> [(Type, Expr)] -> PolyBound SynthSpec -> PolyBound [Expr] -> PolyBound Type -> m [form]
formCalls convExpr funcF tenv meas meas_ex n v_ars si_pb re_pb rt_pb = do
    MaxSize mx_meas <- maxSynthFormSizeM
    inf_con <- infConfigM
    let smt_ars = concatMap (uncurry (adjustArgsWithCare inf_con n convExpr (fromInteger mx_meas) tenv meas meas_ex)) v_ars
        si_re_rt_pb = case filterPBByType snd $ zipPB re_pb rt_pb of
                  Just re_rt_pb -> zipWithPB (\x (y, z) -> (x, y, z)) si_pb re_rt_pb
                  Nothing -> zipWithPB (\x (y, z) -> (x, y, z)) si_pb $ PolyBound ([], headValue rt_pb) [] -- error $ "formCalls: impossible, the polybound should have already been filtered" ++ "\nsi_pb = " ++ show si_pb ++ "\nre_pb = " ++ show re_pb ++ "\nrt_pb = " ++ show rt_pb
    return $ concatMap (\(psi, re, rt) ->
                let
                    f_smt_ars = if null (sy_args psi) then [] else smt_ars
                    smt_r = map (adjustArgs convExpr (fromInteger mx_meas) tenv meas meas_ex rt) re
                in
                map (\r -> funcF (sy_name psi) $ take (length (sy_args psi)) f_smt_ars ++ take (length (sy_rets psi)) r) smt_r
              ) $ extractValues si_re_rt_pb

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
convertConstraint convExpr andF _ _ impF funcF knownF toBeF eenv tenv meas meas_ex evals si (Call All fc hcalls) = do
    pre <- mkPreCall convExpr andF funcF knownF toBeF eenv tenv meas meas_ex evals si fc hcalls
    post <- mkPostCall convExpr andF funcF knownF toBeF eenv tenv meas meas_ex evals si fc
    return $ pre `impF` post
convertConstraint convExpr andF _ _ _ funcF knownF toBeF eenv tenv meas meas_ex evals si (Call Pre fc hcalls) =
    mkPreCall convExpr andF funcF knownF toBeF eenv tenv meas meas_ex evals si fc hcalls
convertConstraint convExpr andF _ _ _ funcF knownF toBeF eenv tenv meas meas_ex evals si (Call Post fc _) =
    mkPostCall convExpr andF funcF knownF toBeF eenv tenv meas meas_ex evals si fc
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

adjustArgsWithCare :: InferenceConfig -> Name -> ConvertExpr form -> Int -> TypeEnv -> Measures -> MeasureExs -> Type -> G2.Expr -> [form]
adjustArgsWithCare inf_con n convExpr mx_meas tenv meas meas_ex t
    | use_invs inf_con
    , specialFunction n =
          map convExpr
        . map adjustLits
        . (\e -> case typeToSort t of Just _ -> [e]; Nothing -> [])
    | otherwise = adjustArgs convExpr mx_meas tenv meas meas_ex t

adjustLits :: G2.Expr -> G2.Expr
adjustLits (App _ l@(Lit _)) = l
adjustLits e = e

validArgForSMT :: G2.Expr -> Bool
validArgForSMT e = not (isLHDict e) && not (isType e)
    where
        isType (Type _) = True
        isType _ = False

        isLHDict e_
            | (TyCon (Name n _ _ _) _):_ <- unTyApp (typeOf e_) = n == "lh"
            | otherwise = False
