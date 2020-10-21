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
import G2.Liquid.Inference.PolyRef

import G2.Solver as Solver

import Control.Monad.IO.Class 

import Language.Haskell.Liquid.Types as LH
import Language.Haskell.Liquid.Types.RefType
import Language.Fixpoint.Types.Constraints
import Language.Fixpoint.Types.Refinements as LH
import qualified Language.Fixpoint.Types as LH
import qualified Language.Fixpoint.Types as LHF

import Data.Coerce
import qualified Data.HashMap.Lazy as HM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Text as T

data SynthRes = SynthEnv GeneratedSpecs | SynthFail FuncConstraints

-- Internal Types
data SpecInfo = SI { s_max_coeff :: Integer
                   , s_prename :: SMTName
                   , s_postname :: SMTName
                   , s_args :: [SpecArg]
                   , s_ret :: SpecArg
                   , s_precoeffs :: [[[SMTName]]]
                   , s_postcoeffs :: [[[SMTName]]]
                   , s_status :: Status }
                   deriving (Show)

data SpecArg = SpecArg { lh_symb :: LH.Symbol
                       , smt_var :: SMTName
                       , smt_sort :: Sort}
               deriving (Show)

data Status = Synth | Known deriving (Eq, Show)

liaSynth :: (InfConfigM m, MonadIO m, SMTConverter con ast out io)
         => con -> [GhcInfo] -> LiquidReadyState -> Evals -> MeasureExs
         -> FuncConstraints -> [Name] -> m SynthRes
liaSynth con ghci lrs evals meas_exs fc ns_synth = do
    -- Compensate for zeroed out names in FuncConstraints
    let ns = map (\(Name n m _ l) -> Name n m 0 l) ns_synth

    -- Figure out the type of each of the functions we need to synthesize
    let eenv = expr_env . state $ lr_state lrs
        tc = type_classes . state $ lr_state lrs
        es = map (\n -> case E.occLookup (nameOcc n) (nameModule n) eenv of
                            Just e' -> e'
                            Nothing -> error $ "synthesize: No expr found") ns
        ts = map (generateRelTypes tc) es

    -- Figure out what the other functions relevant to the current spec are
    let all_calls = concatMap allCallNames $ toListFC fc
        non_ns = filter (`notElem` ns) all_calls
        non_es = map (\n -> case E.occLookup (nameOcc n) (nameModule n) eenv of
                                        Just e' -> e'
                                        Nothing -> error $ "synthesize: No expr found") non_ns
        non_ts = map (generateRelTypes tc) non_es

    liftIO $ putStrLn $ "ns = " ++ show ns
    liftIO $ putStrLn $ "non_ns = " ++ show non_ns
    liftIO $ putStrLn $ "es = " ++ show es
    liftIO $ putStrLn $ "ts = " ++ show ts

    si <- liaSynth' con ghci (zip ns ts) ((zip non_ns non_ts)) fc

    synth con evals si fc

-- addKnownSpecs :: [GhcInfo] -> ExprEnv -> M.Map Name SpecInfo -> FuncConstraints -> M.Map Name SpecInfo
-- addKnownSpecs ghci si =
--     M.foldr (\n si' -> if n `M.member` si'
--                             then si'
--                             else M.insert n (buildSI ghci n  ) si') si . allCallNames fc


liaSynth' :: (InfConfigM m, MonadIO m, SMTConverter con ast out io)
          => con -> [GhcInfo] -> [(Name, ([Type], Type))] -> [(Name, ([Type], Type))] -> FuncConstraints -> m (M.Map Name SpecInfo)
liaSynth' con ghci ns_aty_rty non_ns_aty_rty fc = do
    let si = foldr (\(n, (at, rt)) -> M.insert n (buildSI Synth ghci n at rt)) M.empty ns_aty_rty
        si' = foldr (\(n, (at, rt)) -> M.insert n (buildSI Known ghci n at rt)) si non_ns_aty_rty
        si'' = liaSynthOfSize 1 si'

    return si''

liaSynthOfSize :: Integer -> M.Map Name SpecInfo -> M.Map Name SpecInfo
liaSynthOfSize sz m_si =
    let
        m_si' =
            M.map (\si -> 
                        let
                            pre_c = list_i_j (s_prename si) $ length (s_args si)
                            post_c = list_i_j (s_postname si) $ length (s_args si) + 1
                        in
                        si { s_max_coeff = 5 * sz
                           , s_precoeffs = pre_c
                           , s_postcoeffs = post_c }) m_si
    in
    m_si'
    where
        list_i_j s ars =
            [ 
                [ 
                    [ s ++ "_c_" ++ show j ++ "_t_" ++ show k ++ "_a_" ++ show a
                    | a <- [0..ars]]
                | k <- [1..sz] ]
            | j <- [1..sz] ]

constraintsToSMT :: M.Map Name SpecInfo ->FuncConstraints -> [SMTHeader]
constraintsToSMT si =  map Solver.Assert . map (constraintToSMT si) . toListFC

constraintToSMT :: M.Map Name SpecInfo -> FuncConstraint -> SMTAST
constraintToSMT si (Call All fc) =
    case M.lookup (funcName fc) si of
        Just si' ->
            let
                pre = Func (s_prename si') $ map (exprToSMT . adjustArgs) (arguments fc)
                post = Func (s_postname si') $ map (exprToSMT . adjustArgs) (arguments fc ++ [returns fc])
            in
            pre :=> post
        Nothing -> error "constraintToSMT: specification not found"
constraintToSMT si (Call Pre fc) =
    case M.lookup (funcName fc) si of
        Just si' -> Func (s_prename si') $ map (exprToSMT . adjustArgs) (arguments fc)
        Nothing -> error "constraintToSMT: specification not found"
constraintToSMT si (Call Post fc) =
    case M.lookup (funcName fc) si of
        Just si' -> Func (s_postname si') $ map (exprToSMT . adjustArgs) (arguments fc ++ [returns fc])
        Nothing -> error "constraintToSMT: specification not found"
constraintToSMT si (AndFC fs) = mkSMTAnd $ map (constraintToSMT si) fs
constraintToSMT si (OrFC fs) = mkSMTOr $ map (constraintToSMT si) fs
constraintToSMT si (ImpliesFC fc1 fc2) = constraintToSMT si fc1 :=> constraintToSMT si fc2
constraintToSMT si (NotFC fc) = (:!) (constraintToSMT si fc)

adjustArgs :: G2.Expr -> G2.Expr
adjustArgs (App _ l@(Lit _)) = l
adjustArgs e = e

-- computing F_{Fixed}, i.e. what is the value of known specifications at known points 
envToSMT :: Evals -> M.Map Name SpecInfo -> FuncConstraints -> [SMTHeader]
envToSMT evals si =
     map Solver.Assert
   . concatMap (envToSMT' evals si)
   . concatMap allCalls
   . toListFC

envToSMT' :: Evals -> M.Map Name SpecInfo -> FuncCall -> [SMTAST]
envToSMT' (Evals {pre_evals = pre_ev, post_evals = post_ev}) m_si fc@(FuncCall { funcName = f, arguments = as, returns = r }) =
    case M.lookup f m_si of
        Just si
            | s_status si == Known ->
            let
                smt_as = map (exprToSMT . adjustArgs) as
                smt_r = exprToSMT $ adjustArgs r

                pre_res = case HM.lookup fc pre_ev of
                            Just b -> b
                            Nothing -> error "envToSMT': pre not found"

                post_res = case HM.lookup fc post_ev of
                            Just b -> b
                            Nothing -> error "envToSMT': post not found"

                pre = (if pre_res then id else (:!)) $ Func (s_prename si) smt_as
                post = (if post_res then id else (:!)) $ Func (s_postname si) (smt_as ++ [smt_r])
            in
            [pre, post]
            | otherwise -> []
        Nothing -> error "envToSMT': function not found"

maxCoeffConstraints :: M.Map Name SpecInfo -> [SMTHeader]
maxCoeffConstraints =
      map Solver.Assert
    . concatMap
        (\si ->
            let
                cffs = concat . concat $ s_precoeffs si ++ s_postcoeffs si
            in
            if s_status si == Synth
                then map (\c -> (Neg (VInt (s_max_coeff si)) :<= V c SortInt)
                                    :&& (V c SortInt :<= VInt (s_max_coeff si))) cffs
                else []) . M.elems

synth :: (InfConfigM m, MonadIO m, SMTConverter con ast out io)
      => con -> Evals -> M.Map Name SpecInfo -> FuncConstraints -> m SynthRes
synth con evals m_si fc = do
    let all_precoeffs = getCoeffs s_precoeffs $ M.elems m_si
        all_postcoeffs = getCoeffs s_postcoeffs $ M.elems m_si
        all_coeffs = all_precoeffs ++ all_postcoeffs
    liftIO $ print m_si
    let var_decl_hdrs = map (flip VarDecl SortInt) all_coeffs
        def_funs = concatMap defineLIAFuns $ M.elems m_si
        fc_smt = constraintsToSMT m_si fc
        env_smt = envToSMT evals m_si fc
        max_coeffs = maxCoeffConstraints m_si

        hdrs = var_decl_hdrs ++ def_funs ++ fc_smt ++ env_smt ++ max_coeffs
    -- liftIO . putStrLn $ "hdrs = " ++ show hdrs
    mdl <- liftIO $ checkConstraints con hdrs (zip all_coeffs (repeat SortInt))
    -- liftIO . putStrLn $ "mdl = " ++ show mdl
    case mdl of
        Just mdl' -> do
            let lh_spec = M.map (\si -> buildLIA_LH si mdl') . M.filter (\si -> s_status si == Synth) $ m_si
            liftIO $ print lh_spec
            let gs' = M.foldrWithKey insertAssertGS emptyGS
                    $ M.map (map (flip PolyBound [])) lh_spec
            liftIO $ print gs'
            return (SynthEnv gs')
        Nothing -> undefined
    where
        getCoeffs f = concat . concat . concatMap f . filter (\si -> s_status si == Synth)


defineLIAFuns :: SpecInfo -> [SMTHeader]
defineLIAFuns si =
    let
        pre_ars_nm = map smt_var (s_args si)
        pre_ars = zip pre_ars_nm (repeat SortInt)

        post_ars_nm = pre_ars_nm ++ [smt_var $ s_ret si]
        post_ars = zip post_ars_nm (repeat SortInt)
    in
    if s_status si == Synth
        then [ DefineFun (s_prename si) pre_ars SortBool (buildLIA_SMT (s_precoeffs si) pre_ars_nm)
             , DefineFun (s_postname si) post_ars SortBool (buildLIA_SMT (s_postcoeffs si) post_ars_nm)]
        else [ DeclareFun (s_prename si) (map snd pre_ars) SortBool
             , DeclareFun (s_postname si) (map snd post_ars) SortBool]

--------------------------------------------------
-- Building LIA formulas, both for SMT and LH

type Plus a = a ->  a -> a
type Mult a = a ->  a -> a
type GEq a b = a -> a -> b
type And b c = [b] -> c
type Or b = [b] -> b
type VInt a = SMTName -> a
type CInt a = Integer -> a

buildLIA_SMT :: [[[SMTName]]] -> [SMTName] -> SMTAST
buildLIA_SMT = buildLIA (:+) (:*) (:>=) mkSMTAnd mkSMTOr (flip V SortInt) VInt

-- Get a list of all LIA formulas.  We must then assign these to the "correct" refinement type,
-- i.e. the refinement type that is closest to the left, while still having all relevant variables bound.
buildLIA_LH :: SpecInfo -> SMTModel -> [LHF.Expr]
buildLIA_LH si mv =
    let
        build = buildLIA ePlus eTimes bGeq PAnd POr detVar (ECon . I) -- todo: Probably want to replace PAnd with id to group?
        pre = build (s_precoeffs si) (map smt_var (s_args si))
        post = build (s_postcoeffs si) (map smt_var (s_args si) ++ [smt_var $ s_ret si])
    in
    [pre, post]
    where
        detVar v 
            | Just (VInt c) <- M.lookup v mv = ECon (I c)
            | Just sa <- L.find (\sa_ -> v == smt_var sa_) (s_ret si:s_args si) = EVar (lh_symb sa)
            | otherwise = error "detVar: variable not found"

        eTimes (ECon (I 0)) _ = ECon (I 0)
        eTimes _ (ECon (I 0)) = ECon (I 0)
        eTimes x y = EBin LH.Times x y

        ePlus (ECon (I 0)) x = x
        ePlus x (ECon (I 0)) = x
        ePlus x y = EBin LH.Plus x y

        bGeq x y
            | x == y = PTrue
            | otherwise = PAtom LH.Ge x y

buildLIA :: Plus a
         -> Mult a
         -> GEq a b
         -> And b c
         -> Or b
         -> VInt a
         -> CInt a
         -> [[[SMTName]]]
         -> [SMTName]
         -> c
buildLIA plus mult geq mk_and mk_or vint cint all_coeffs args =
    let
        lin_ineqs = map (map toLinInEqs) all_coeffs
    in
    mk_and . map mk_or $ lin_ineqs
    where
        toLinInEqs (c:cs) =
            let
                sm = foldr plus (vint c)
                   . map (uncurry mult)
                   $ zip (map vint cs) (map vint args)
            in
            sm `geq` cint 0
        toLinInEqs [] = error "buildLIA: unhandled empty coefficient list" 
--------------------------------------------------

buildSI :: Status -> [GhcInfo] ->  Name -> [Type] -> Type -> SpecInfo
buildSI stat ghci f aty rty =
    let
        smt_f = nameToStr f
        fspec = case genSpec ghci f of
                Just spec' -> spec'
                _ -> error $ "synthesize: No spec found for " ++ show f
        (ars, ret) = argsAndRetFromFSpec [] aty rty fspec
    in
    SI { s_prename = smt_f ++ "_pre"
       , s_postname = smt_f ++ "_post"
       , s_args = map (\(a, i) -> a { smt_var = "x_" ++ show i } ) $ zip ars [1..]
       , s_ret = ret { smt_var = "x_r" }
       , s_precoeffs = []
       , s_postcoeffs = []
       , s_status = stat }
    
argsAndRetFromFSpec :: [SpecArg] -> [Type] -> Type -> SpecType -> ([SpecArg], SpecArg)
argsAndRetFromFSpec ars (_:ts) rty (RAllT { rt_ty = out }) = argsAndRetFromFSpec ars ts rty out
argsAndRetFromFSpec ars (t:ts) rty (RFun { rt_bind = b, rt_in = i, rt_out = out}) =
    let
        sa = SpecArg { lh_symb = b
                     , smt_var = undefined
                     , smt_sort = typeToSort t} 
    in
    case i of
        RFun {} -> argsAndRetFromFSpec ars ts rty out
        _ -> argsAndRetFromFSpec (sa:ars) ts rty out
argsAndRetFromFSpec ars _ rty (RApp { rt_reft = ref}) =
    let
        sa = SpecArg { lh_symb = reftSymbol $ ur_reft ref
                     , smt_var = undefined
                     , smt_sort = typeToSort rty} 
    in
    (reverse ars, sa)
argsAndRetFromFSpec ars _ rty (RVar { rt_reft = ref}) =
    let
        sa = SpecArg { lh_symb = reftSymbol $ ur_reft ref
                     , smt_var = undefined
                     , smt_sort = typeToSort rty } 
    in
    (reverse ars, sa)


reftSymbol :: Reft -> LH.Symbol
reftSymbol = fst . unpackReft

unpackReft :: Reft -> (LH.Symbol, LH.Expr) 
unpackReft = coerce

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