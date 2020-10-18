{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.Sygus.LiaSynth ( SynthRes (..)
                                          , liaSynth) where

import G2.Language as G2
import qualified G2.Language.ExprEnv as E
import G2.Liquid.Interface
import G2.Liquid.Types
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.FuncConstraint
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.GeneratedSpecs

import G2.Solver as Solver

import Control.Monad.IO.Class 

import Language.Haskell.Liquid.Types as LH
import Language.Haskell.Liquid.Types.RefType
import Language.Fixpoint.Types.Constraints
import Language.Fixpoint.Types.Refinements as LH
import qualified Language.Fixpoint.Types as LH
import qualified Language.Fixpoint.Types as LHF

import qualified Data.Map as M

data SynthRes = SynthEnv GeneratedSpecs | SynthFail FuncConstraints

-- Internal Types
data SpecInfo = SI { s_prename :: SMTName
                   , s_postname :: SMTName
                   , s_args :: [Sort]
                   , s_ret :: Sort
                   , s_precoeffs :: [[[SMTName]]]
                   , s_postcoeffs :: [[[SMTName]]] }
                   deriving (Show)

liaSynth :: (InfConfigM m, MonadIO m, SMTConverter con ast out io)
         => con -> [GhcInfo] -> LiquidReadyState -> MeasureExs
         -> FuncConstraints -> [Name] -> m SynthRes
liaSynth con ghci lrs meas_exs fcs ns = do
    -- Figure out the type of each of the functions
    let eenv = expr_env . state $ lr_state lrs
        tc = type_classes . state $ lr_state lrs
        es = map (\n -> case E.occLookup (nameOcc n) (nameModule n) eenv of
                            Just e' -> e'
                            Nothing -> error $ "synthesize: No expr found") ns
        ts = map (generateRelTypes tc) es

    liftIO $ putStrLn $ "ns = " ++ show ns
    liftIO $ putStrLn $ "es = " ++ show es
    liftIO $ putStrLn $ "ts = " ++ show ts

    liaSynth' con (zip ns ts) fcs

liaSynth' :: (InfConfigM m, MonadIO m, SMTConverter con ast out io)
          => con -> [(Name, ([Type], Type))] -> FuncConstraints -> m SynthRes
liaSynth' con ns_aty_rty fc = do
    let si = foldr (\(n, (at, rt)) -> M.insert n (buildSI n at rt)) M.empty ns_aty_rty
    let si' = liaSynthOfSize 2 si
    synth con si' fc

liaSynthOfSize :: Int -> M.Map Name SpecInfo -> M.Map Name SpecInfo
liaSynthOfSize sz m_si =
    let
        (_, m_si') =
            M.mapAccum (\i si -> 
                            let
                                pre_c = list_i_j "pre_c" i $ length (s_args si)
                                post_c = list_i_j "post_c" i $ length (s_args si) + 1
                            in
                            (i + 1, si { s_precoeffs = pre_c
                                       , s_postcoeffs = post_c })) (0 :: Int) m_si
    in
    m_si'
    where
        list_i_j s i ars =
            [ 
                [ 
                    [ s ++ "_" ++ show i ++ "_c_" ++ show j ++ "_t_" ++ show k ++ "_a_" ++ show a
                    | a <- [0..ars]]
                | k <- [0..sz] ]
            | j <- [0..sz] ]

constraintsToSMT :: M.Map Name SpecInfo ->FuncConstraints -> [SMTHeader]
constraintsToSMT si =  map Solver.Assert . map (constraintToSMT si) . toListFC

constraintToSMT :: M.Map Name SpecInfo -> FuncConstraint -> SMTAST
constraintToSMT si (Call All fc) =
    case M.lookup (funcName fc) si of
        Just si' ->
            let
                pre = Func (s_prename si') $ map exprToSMT (arguments fc ++ [returns fc])
                post = Func (s_postname si') $ map exprToSMT (arguments fc ++ [returns fc])
            in
            pre :=> post
        Nothing -> error "constraintToSMT: specification not found"
constraintToSMT si (Call Pre fc) =
    case M.lookup (funcName fc) si of
        Just si' -> Func (s_prename si') $ map exprToSMT (arguments fc ++ [returns fc])
        Nothing -> error "constraintToSMT: specification not found"
constraintToSMT si (Call Post fc) =
    case M.lookup (funcName fc) si of
        Just si' -> Func (s_postname si') $ map exprToSMT (arguments fc ++ [returns fc])
        Nothing -> error "constraintToSMT: specification not found"
constraintToSMT si (AndFC fs) = mkSMTAnd $ map (constraintToSMT si) fs
constraintToSMT si (OrFC fs) = mkSMTOr $ map (constraintToSMT si) fs
constraintToSMT si (ImpliesFC fc1 fc2) = constraintToSMT si fc1 :=> constraintToSMT si fc2
constraintToSMT si (NotFC fc) = Neg (constraintToSMT si fc)

synth :: (InfConfigM m, MonadIO m, SMTConverter con ast out io)
      => con -> M.Map Name SpecInfo -> FuncConstraints -> m SynthRes
synth con si fc = do
    let all_precoeffs = concat . concat . concatMap s_precoeffs $ M.elems si
        all_postcoeffs = concat . concat . concatMap s_postcoeffs $ M.elems si
        all_coeffs = all_precoeffs ++ all_postcoeffs
    liftIO $ print si
    let var_decl_hdrs = map (flip VarDecl SortInt) all_coeffs
        def_funs = concatMap defineLIAFuns $ M.elems si
        fc_smt = constraintsToSMT si fc

        hdrs = var_decl_hdrs ++ def_funs ++ fc_smt
    liftIO $ print hdrs
    liftIO $ print =<< checkConstraints con hdrs (zip all_coeffs (repeat SortInt))
    undefined

--------------------------------------------------
-- Helper functions for liaSynthOfSize
defineLIAFuns :: SpecInfo -> [SMTHeader]
defineLIAFuns si =
    let
        pre_ars_nm = map (\i -> "x_" ++ show i) [1..length (s_args si)]
        pre_ars = zip pre_ars_nm (repeat SortInt)

        post_ars_nm = map (\i -> "x_" ++ show i) [1..length (s_args si) + 1]
        post_ars = zip post_ars_nm (repeat SortInt)
    in
    [ DefineFun (s_prename si) pre_ars SortBool (buildFunBody (s_precoeffs si) pre_ars_nm)
    , DefineFun (s_postname si) post_ars SortBool (buildFunBody (s_postcoeffs si) post_ars_nm)]

buildFunBody :: [[[SMTName]]] -> [SMTName] -> SMTAST
buildFunBody all_coeffs args =
    let
        lin_ineqs = map (map toLinInEqs) all_coeffs :: [[SMTAST]]
    in
    mkSMTAnd . map mkSMTOr $ lin_ineqs
    where
        toLinInEqs :: [SMTName] -> SMTAST
        toLinInEqs (c:cs) =
            let
                sm = foldr (:+) (V c SortInt)
                   . map (uncurry (:*))
                   $ zip (map (flip V SortInt) cs) (map (flip V SortInt) args)
            in
            sm :> (VInt 0)
        toLinInEqs [] = error "buildFunBody: unhandled empty coefficient list" 
--------------------------------------------------

buildSI :: Name -> [Type] -> Type -> SpecInfo
buildSI n aty rty =
    let
        smt_n = nameToStr n
    in
    SI { s_prename = smt_n ++ "_pre"
       , s_postname = smt_n ++ "_post"
       , s_args = map typeToSort aty
       , s_ret = typeToSort rty
       , s_precoeffs = []
       , s_postcoeffs = [] }

generateRelTypes :: TypeClasses -> G2.Expr -> ([Type], Type)
generateRelTypes tc e =
    let
        ty_e = PresType $ inTyForAlls (typeOf e)
        arg_ty_c = filter (not . isTYPE)
                 . filter (not . isTypeClass tc)
                 $ argumentTypes ty_e
        ret_ty_c = returnType ty_e
    in
    (arg_ty_c, ret_ty_c)

typeToSort :: Type -> Sort
typeToSort (TyCon (Name n _ _ _) _) 
    | n == "Int"  = SortInt
    | n == "Double"  = SortDouble
typeToSort _ = error "typeToSort: Unsupported type"