{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.Sygus.LiaSynth ( SynthRes (..)
                                          , liaSynth) where

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

import Language.Haskell.Liquid.Types as LH
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
import qualified Data.Text as T

import Debug.Trace

data SynthRes = SynthEnv GeneratedSpecs | SynthFail FuncConstraints

type Coeffs = [SMTName]
type Clause = [Coeffs] 
type CNF = [Clause]

-- Internal Types
data SpecInfo = SI { s_max_coeff :: Integer
                   
                   -- A function that is defined as the conjunction the known and synthesized functions.
                   , s_pre :: FixedSpec
                   , s_post :: FixedSpec

                   -- A function that is used to record the value of the function at known points,
                   -- i.e. points that occur in the FuncConstraints
                   , s_known_pre :: FixedSpec
                   , s_known_post :: FixedSpec

                   -- Functions that capture the pre and post condition.
                   -- We have one precondition function per argument
                   , s_syn_pre :: [SynthSpec]
                   , s_syn_post :: SynthSpec

                   , s_status :: Status }
                   deriving (Show)

s_pre_name :: SpecInfo -> SMTName
s_pre_name = fs_name . s_pre

s_pre_args :: SpecInfo -> [SpecArg]
s_pre_args = fs_args . s_pre

s_post_name :: SpecInfo -> SMTName
s_post_name = fs_name . s_post

s_post_args :: SpecInfo -> [SpecArg]
s_post_args = fs_args . s_post

s_known_pre_name :: SpecInfo -> SMTName
s_known_pre_name = fs_name . s_known_pre

s_known_pre_args :: SpecInfo -> [SpecArg]
s_known_pre_args = fs_args . s_known_pre

s_known_post_name :: SpecInfo -> SMTName
s_known_post_name = fs_name . s_known_post

s_known_post_args :: SpecInfo -> [SpecArg]
s_known_post_args = fs_args . s_known_post

data FixedSpec = FixedSpec { fs_name :: SMTName
                           , fs_args :: [SpecArg] }
                           deriving (Show)

data SynthSpec = SynthSpec { sy_name :: SMTName
                           , sy_args :: [SpecArg]
                           , sy_coeffs :: CNF }
                           deriving (Show)

data SpecArg = SpecArg { lh_rep :: LH.Expr
                       , smt_var :: SMTName
                       , smt_sort :: Sort}
                       deriving (Show)

data Status = Synth | Known deriving (Eq, Show)

liaSynth :: (InfConfigM m, MonadIO m, SMTConverter con ast out io)
         => con -> [GhcInfo] -> LiquidReadyState -> Evals -> MeasureExs
         -> FuncConstraints -> [Name] -> m SynthRes
liaSynth con ghci lrs evals meas_ex fc ns_synth = do
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

    si <- liaSynth' con ghci lrs (zip ns ts) ((zip non_ns non_ts)) meas_ex fc

    liftIO . putStrLn $ "si = " ++ show si

    synth con meas_ex evals si fc

-- addKnownSpecs :: [GhcInfo] -> ExprEnv -> M.Map Name SpecInfo -> FuncConstraints -> M.Map Name SpecInfo
-- addKnownSpecs ghci si =
--     M.foldr (\n si' -> if n `M.member` si'
--                             then si'
--                             else M.insert n (buildSI ghci n  ) si') si . allCallNames fc


liaSynth' :: (InfConfigM m, MonadIO m, SMTConverter con ast out io)
          => con -> [GhcInfo] -> LiquidReadyState -> [(Name, ([Type], Type))] -> [(Name, ([Type], Type))] -> MeasureExs -> FuncConstraints -> m (M.Map Name SpecInfo)
liaSynth' con ghci lrs ns_aty_rty non_ns_aty_rty meas_exs fc = do
    let meas = lrsMeasures ghci lrs

    let si = foldr (\(n, (at, rt)) -> M.insert n (buildSI meas Synth ghci n at rt)) M.empty ns_aty_rty
        si' = foldr (\(n, (at, rt)) -> M.insert n (buildSI meas Known ghci n at rt)) si non_ns_aty_rty
        si'' = liaSynthOfSize 1 si'

    return si''

liaSynthOfSize :: Integer -> M.Map Name SpecInfo -> M.Map Name SpecInfo
liaSynthOfSize sz m_si =
    let
        m_si' =
            M.map (\si -> 
                    let
                        s_syn_pre' = map (\psi ->
                                        psi { sy_coeffs = list_i_j (sy_name psi) $ length (sy_args psi) }
                                     ) (s_syn_pre si)
                        post_c = list_i_j (sy_name $ s_syn_post si) $ length (sy_args $ s_syn_post si)
                    in
                    si { s_syn_pre = s_syn_pre' -- (s_syn_pre si) { sy_coeffs = pre_c }
                       , s_syn_post = (s_syn_post si) { sy_coeffs = post_c }
                       , s_max_coeff = 5 * sz }) m_si
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

constraintsToSMT :: MeasureExs -> M.Map Name SpecInfo ->FuncConstraints -> [SMTHeader]
constraintsToSMT meas_ex si =  map Solver.Assert . map (constraintToSMT meas_ex si) . toListFC

constraintToSMT :: MeasureExs -> M.Map Name SpecInfo -> FuncConstraint -> SMTAST
constraintToSMT meas_ex si (Call All fc) =
    case M.lookup (funcName fc) si of
        Just si' ->
            let
                pre = Func (s_pre_name si') . map exprToSMT . concatMap (adjustArgs meas_ex) $ arguments fc
                post = Func (s_post_name si') . map exprToSMT . concatMap (adjustArgs meas_ex) $ arguments fc ++ [returns fc]
            in
            pre :=> post
        Nothing -> error "constraintToSMT: specification not found"
constraintToSMT meas_ex si (Call Pre fc) =
    case M.lookup (funcName fc) si of
        Just si' ->
            Func (s_pre_name si') . map exprToSMT . concatMap (adjustArgs meas_ex) $ arguments fc
        Nothing -> error $ "constraintToSMT: specification not found" ++ show fc
constraintToSMT meas_ex si (Call Post fc) =
    case M.lookup (funcName fc) si of
        Just si' -> Func (s_post_name si') . map exprToSMT . concatMap (adjustArgs meas_ex) $ arguments fc ++ [returns fc]
        Nothing -> error "constraintToSMT: specification not found"
constraintToSMT meas_ex si (AndFC fs) = mkSMTAnd $ map (constraintToSMT meas_ex si) fs
constraintToSMT meas_ex si (OrFC fs) = mkSMTOr $ map (constraintToSMT meas_ex si) fs
constraintToSMT meas_ex si (ImpliesFC fc1 fc2) = constraintToSMT meas_ex si fc1 :=> constraintToSMT meas_ex si fc2
constraintToSMT meas_ex si (NotFC fc) = (:!) (constraintToSMT meas_ex si fc)

adjustArgs :: MeasureExs -> G2.Expr -> [G2.Expr]
adjustArgs meas_ex = map adjustLits . substMeasures meas_ex

substMeasures :: MeasureExs -> G2.Expr -> [G2.Expr]
substMeasures meas_ex e =
    case typeToSort (typeOf e) of
        Just _ -> [e]
        Nothing ->
            case HM.lookup e meas_ex of
                Just es ->
                    -- Sort to make sure we get the same order consistently
                    map snd . L.sortBy (\(n1, _) (n2, _) -> compare n1 n2) $ HM.toList es
                Nothing -> []

adjustLits :: G2.Expr -> G2.Expr
adjustLits (App _ l@(Lit _)) = l
adjustLits e = e

-- computing F_{Fixed}, i.e. what is the value of known specifications at known points 
envToSMT :: MeasureExs -> Evals -> M.Map Name SpecInfo -> FuncConstraints -> [SMTHeader]
envToSMT meas_ex evals si =
     map Solver.Assert
   . concatMap (uncurry (envToSMT' meas_ex evals si))
   . flip zip ["f" ++ show i | i <-[1..]]
   . L.nub
   . concatMap allCalls
   . toListFC

envToSMT' :: MeasureExs -> Evals -> M.Map Name SpecInfo -> FuncCall -> SMTName -> [SMTAST]
envToSMT' meas_ex (Evals {pre_evals = pre_ev, post_evals = post_ev}) m_si fc@(FuncCall { funcName = f, arguments = as, returns = r }) uc_n =
    case M.lookup f m_si of
        Just si ->
            let
                smt_as = map exprToSMT $ concatMap (adjustArgs meas_ex) as
                smt_r = map exprToSMT $ (adjustArgs meas_ex) r

                pre_res = case HM.lookup fc pre_ev of
                            Just b -> b
                            Nothing -> error "envToSMT': pre not found"

                post_res = case HM.lookup fc post_ev of
                            Just b -> b
                            Nothing -> error "envToSMT': post not found"

                pre = (if pre_res then id else (:!)) $ Func (s_known_pre_name si) smt_as
                post = (if post_res then id else (:!)) $ Func (s_known_post_name si) (smt_as ++ smt_r)
            in
            [Named pre ("pre_" ++ uc_n), Named post ("post_" ++ uc_n)]
        Nothing -> error "envToSMT': function not found"

maxCoeffConstraints :: M.Map Name SpecInfo -> [SMTHeader]
maxCoeffConstraints =
      map Solver.Assert
    . concatMap
        (\si ->
            let
                cffs = concat . concat $ allPreCoeffs si ++ sy_coeffs (s_syn_post si)
            in
            if s_status si == Synth
                then map (\c -> (Neg (VInt (s_max_coeff si)) :<= V c SortInt)
                                    :&& (V c SortInt :<= VInt (s_max_coeff si))) cffs
                else []) . M.elems

linkPreFuncs :: M.Map Name SpecInfo -> [SMTHeader]
linkPreFuncs = map linkPreFunc . M.elems

linkPreFunc :: SpecInfo -> SMTHeader
linkPreFunc si =
    let
        ars = zip (map smt_var $ s_pre_args si) (repeat SortInt)

        sy_body = foldr (\psi e ->
                            let
                                p_ars = take (length $ sy_args psi) ars
                            in
                            Func (sy_name psi) (map (uncurry V) p_ars) :&& e) (VBool True) (s_syn_pre si)
        fixed_body = Func (s_known_pre_name si) (map (uncurry V) ars)
        body = case s_status si of
                Synth -> fixed_body :&& sy_body
                Known -> fixed_body
    in
    DefineFun (s_pre_name si) ars SortBool body

linkPostFuncs :: M.Map Name SpecInfo -> [SMTHeader]
linkPostFuncs = map linkPostFunc . M.elems

linkPostFunc :: SpecInfo -> SMTHeader
linkPostFunc si = 
    let
        ars = zip (map smt_var $ s_post_args si) (repeat SortInt)

        sy_body = Func (sy_name $ s_syn_post si) (map (uncurry V) ars)
        fixed_body = Func (s_known_post_name si) (map (uncurry V) ars)
        body = case s_status si of
                Synth -> fixed_body :&& sy_body
                Known -> fixed_body
    in
    DefineFun (s_post_name si) ars SortBool body

synth :: (InfConfigM m, MonadIO m, SMTConverter con ast out io)
      => con -> MeasureExs -> Evals -> M.Map Name SpecInfo -> FuncConstraints -> m SynthRes
synth con meas_ex evals m_si fc = do
    let all_precoeffs = getCoeffs allPreCoeffs $ M.elems m_si
        all_postcoeffs = getCoeffs (sy_coeffs . s_syn_post) $ M.elems m_si
        all_coeffs = all_precoeffs ++ all_postcoeffs
    liftIO $ print m_si
    let var_decl_hdrs = map (flip VarDecl SortInt) all_coeffs
        def_funs = concatMap defineLIAFuns $ M.elems m_si
        link_pre = linkPreFuncs m_si
        link_post = linkPostFuncs m_si
        fc_smt = constraintsToSMT meas_ex m_si fc
        env_smt = envToSMT meas_ex evals m_si fc
        max_coeffs = maxCoeffConstraints m_si

        hdrs = var_decl_hdrs ++ def_funs ++ link_pre ++ link_post ++ fc_smt ++ env_smt ++ max_coeffs
    -- liftIO . putStrLn $ "hdrs = " ++ show hdrs
    mdl <- liftIO $ constraintsToModelOrUnsatCore con hdrs (zip all_coeffs (repeat SortInt))
    -- liftIO . putStrLn $ "mdl = " ++ show mdl
    case mdl of
        Right mdl' -> do
            let lh_spec = M.map (\si -> buildLIA_LH si mdl') . M.filter (\si -> s_status si == Synth) $ m_si
            liftIO $ print lh_spec
            let gs' = M.foldrWithKey insertAssertGS emptyGS
                    $ M.map (map (flip PolyBound [])) lh_spec
            liftIO $ print gs'
            return (SynthEnv gs')
        Left uc -> undefined
    where
        getCoeffs f = concat . concat . concatMap f . filter (\si -> s_status si == Synth)


defineLIAFuns :: SpecInfo -> [SMTHeader]
defineLIAFuns si =
    (if s_status si == Synth
        then 
             defineSynthLIAFuncSF (s_syn_post si)
            :map defineSynthLIAFuncSF (s_syn_pre si)
        else [])
    ++
    [ defineFixedLIAFuncSF (s_known_pre si)
    , defineFixedLIAFuncSF (s_known_post si)]

defineFixedLIAFuncSF :: FixedSpec -> SMTHeader
defineFixedLIAFuncSF fs =
    let
        ars = map (const SortInt) (fs_args fs)
    in
    DeclareFun (fs_name fs) ars SortBool

defineSynthLIAFuncSF :: SynthSpec -> SMTHeader
defineSynthLIAFuncSF sf = 
    let
        ars_nm = map smt_var (sy_args sf)
        ars = zip ars_nm (repeat SortInt)
    in
    DefineFun (sy_name sf) ars SortBool (buildLIA_SMT (sy_coeffs sf) ars_nm)

declareSynthLIAFuncSF :: SynthSpec -> SMTHeader
declareSynthLIAFuncSF sf =
    let
        ars = map (const SortInt) (sy_args sf)
    in
    DeclareFun (sy_name sf) (ars) SortBool

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
        pre = map (\psi -> build (sy_coeffs psi) (map smt_var (sy_args psi))) (s_syn_pre si)
        post = build (sy_coeffs (s_syn_post si)) (map smt_var (sy_args $ s_syn_post si))
    in
    pre ++ [post]
    where
        detVar v 
            | Just (VInt c) <- M.lookup v mv = ECon (I c)
            | Just sa <- L.find (\sa_ -> v == smt_var sa_) (allPreSpecArgs si ++ sy_args (s_syn_post si)) = lh_rep sa
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

buildSI :: Measures -> Status -> [GhcInfo] ->  Name -> [Type] -> Type -> SpecInfo
buildSI meas stat ghci f aty rty =
    let
        smt_f = nameToStr f
        fspec = case genSpec ghci f of
                Just spec' -> spec'
                _ -> error $ "synthesize: No spec found for " ++ show f
        (ars, ret) = argsAndRetFromFSpec ghci meas [] aty rty fspec

        arg_ns = map (\(a, i) -> a { smt_var = "x_" ++ show i } ) $ zip (concat ars) [1..]
        ret_ns = map (\(r, i) -> r { smt_var = "x_r_" ++ show i }) $ zip ret [1..]
    in
    SI { s_pre = FixedSpec { fs_name = smt_f ++ "_pre"
                           , fs_args = arg_ns }
       , s_post = FixedSpec { fs_name = smt_f ++ "_post"
                            , fs_args = arg_ns ++ ret_ns }
       , s_known_pre = FixedSpec { fs_name = smt_f ++ "_known_pre"
                                 , fs_args = arg_ns }
       , s_known_post = FixedSpec { fs_name = smt_f ++ "_known_post"
                                  , fs_args = arg_ns ++ ret_ns }
       , s_syn_pre = map (\(ars', i) ->
                            SynthSpec { sy_name = smt_f ++ "_synth_pre_" ++ show i
                                      , sy_args = map (\(a, j) -> a { smt_var = "x_" ++ show j}) $ zip ars' [1..]
                                      , sy_coeffs = [] 
                                      }
                     ) $ zip ars [1..]
       , s_syn_post = SynthSpec { sy_name = smt_f ++ "_synth_post"
                                , sy_args = arg_ns ++ ret_ns
                                , sy_coeffs = [] }
       , s_status = stat }

argsAndRetFromFSpec :: [GhcInfo] -> Measures -> [[SpecArg]] -> [Type] -> Type -> SpecType -> ([[SpecArg]], [SpecArg])
argsAndRetFromFSpec ghci meas ars (_:ts) rty (RAllT { rt_ty = out }) =
    argsAndRetFromFSpec ghci meas ars ts rty out
argsAndRetFromFSpec ghci meas ars (t:ts) rty (RFun { rt_bind = b, rt_in = i, rt_out = out}) =
    let
        sa = mkSpecArg ghci meas b t
    in
    case i of
        RFun {} -> argsAndRetFromFSpec ghci meas ars ts rty out
        _ -> argsAndRetFromFSpec ghci meas (sa:ars) ts rty out
argsAndRetFromFSpec ghci meas ars _ rty (RApp { rt_reft = ref}) =
    let
        sa = mkSpecArg ghci meas (reftSymbol $ ur_reft ref) rty
    in
    (reverse ars, sa)
argsAndRetFromFSpec ghci meas ars _ rty (RVar { rt_reft = ref}) =
    let
        sa = mkSpecArg ghci meas (reftSymbol $ ur_reft ref) rty
    in
    (reverse ars, sa)

mkSpecArg :: [GhcInfo] -> Measures -> LH.Symbol -> Type -> [SpecArg]
mkSpecArg ghci meas symb t =
    let
        srt = typeToSort t
    in
    case srt of
        Just srt' ->
            [SpecArg { lh_rep = EVar symb
                     , smt_var = undefined
                     , smt_sort = srt' }]
        Nothing ->
            let
                app_meas = applicableMeasures meas t
                app_meas' = L.sortBy (\(n1, _) (n2, _) -> compare n1 n2) app_meas
            in
            mapMaybe
                (\(mn, mt) ->
                    fmap (\srt' ->
                            let
                                lh_mn = getLHMeasureName ghci mn
                            in
                            SpecArg { lh_rep = EApp (EVar lh_mn) (EVar symb)
                                    , smt_var = undefined
                                    , smt_sort = srt'}) $ typeToSort mt) app_meas'



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

applicableMeasures :: Measures -> Type -> [(Name, Type)]
applicableMeasures meas t =
    HM.toList . E.map' returnType $ E.filter (applicableMeasure t) meas 

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
allPreCoeffs :: SpecInfo -> CNF
allPreCoeffs = concatMap sy_coeffs . s_syn_pre

allPreSpecArgs :: SpecInfo -> [SpecArg]
allPreSpecArgs = concatMap sy_args . s_syn_pre
