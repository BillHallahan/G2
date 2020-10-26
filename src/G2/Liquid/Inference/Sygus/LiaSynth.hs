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
import Data.Monoid (Sum (..))
import qualified Data.Text as T

import Debug.Trace

data SynthRes = SynthEnv GeneratedSpecs | SynthFail FuncConstraints

type Coeffs = [SMTName]
type Clause = [Coeffs] 
type CNF = [Clause]

-- Internal Types
data SpecInfo = SI { s_max_coeff :: Integer
                   
                   -- A function that is used to record the value of the function at known points,
                   -- i.e. points that occur in the FuncConstraints
                   , s_known_pre :: FixedSpec
                   , s_known_post :: FixedSpec

                   -- Functions that capture the pre and post condition.
                   -- We have one precondition function per argument
                   , s_syn_pre :: [SynthSpec]
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
         => con -> [GhcInfo] -> LiquidReadyState -> Evals Bool -> MeasureExs
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

    let si = buildSpecInfo con ghci lrs (zip ns ts) ((zip non_ns non_ts)) meas_ex fc

    -- liftIO . putStrLn $ "si = " ++ show si

    synth con meas_ex evals si fc 1

-- addKnownSpecs :: [GhcInfo] -> ExprEnv -> M.Map Name SpecInfo -> FuncConstraints -> M.Map Name SpecInfo
-- addKnownSpecs ghci si =
--     M.foldr (\n si' -> if n `M.member` si'
--                             then si'
--                             else M.insert n (buildSI ghci n  ) si') si . allCallNames fc


buildSpecInfo :: con -> [GhcInfo] -> LiquidReadyState -> [(Name, ([Type], Type))] -> [(Name, ([Type], Type))]
              -> MeasureExs -> FuncConstraints -> M.Map Name SpecInfo
buildSpecInfo con ghci lrs ns_aty_rty non_ns_aty_rty meas_exs fc =
    let 
        meas = lrsMeasures ghci lrs

        si = foldr (\(n, (at, rt)) -> M.insert n (buildSI meas Synth ghci n at rt)) M.empty ns_aty_rty
        si' = foldr (\(n, (at, rt)) -> M.insert n (buildSI meas Known ghci n at rt)) si non_ns_aty_rty
    in
    si'

liaSynthOfSize :: Integer -> M.Map Name SpecInfo -> M.Map Name SpecInfo
liaSynthOfSize sz m_si =
    let
        m_si' =
            M.map (\si -> 
                    let
                        s_syn_pre' =
                            map (\psi ->
                                    psi { sy_coeffs = list_i_j (sy_name psi) $ length (sy_args psi) }
                                 ) (s_syn_pre si)
                        s_syn_post' =
                            mapPB (\psi -> 
                                        psi { sy_coeffs = list_i_j (sy_name psi) $ length (sy_args psi) }
                                  ) (s_syn_post si)
                    in
                    si { s_syn_pre = s_syn_pre' -- (s_syn_pre si) { sy_coeffs = pre_c }
                       , s_syn_post = s_syn_post' -- (s_syn_post si) { sy_coeffs = post_c }
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

type Size = Integer

synth :: (InfConfigM m, MonadIO m, SMTConverter con ast out io)
      => con -> MeasureExs -> Evals Bool -> M.Map Name SpecInfo -> FuncConstraints -> Size -> m SynthRes
synth con meas_ex evals si fc sz = do
    let si' = liaSynthOfSize sz si
    res <- synth' con meas_ex evals si' fc
    case res of
        SynthEnv _ -> return res
        SynthFail _ -> synth con meas_ex evals si fc (sz + 1)

synth' :: (InfConfigM m, MonadIO m, SMTConverter con ast out io)
      => con -> MeasureExs -> Evals Bool -> M.Map Name SpecInfo -> FuncConstraints -> m SynthRes
synth' con meas_ex evals m_si fc = do
    let all_coeffs = getCoeffs m_si
    liftIO $ print m_si
    let evals' = assignIds evals
        cons = nonMaxCoeffConstraints meas_ex evals' m_si fc
        max_coeffs_cons = maxCoeffConstraints m_si

        hdrs = cons ++ max_coeffs_cons

    mdl <- liftIO $ constraintsToModelOrUnsatCore con hdrs (zip all_coeffs (repeat SortInt))

    case mdl of
        Right mdl' -> do
            let lh_spec = M.map (\si -> buildLIA_LH si mdl') . M.filter (\si -> s_status si == Synth) $ m_si
            liftIO $ print lh_spec
            let gs' = M.foldrWithKey insertAssertGS emptyGS lh_spec
            liftIO $ print gs'
            return (SynthEnv gs')
        Left uc -> return (SynthFail undefined)

mkPreCall :: MeasureExs -> Evals (Integer, Bool) -> M.Map Name SpecInfo -> FuncCall -> SMTAST
mkPreCall meas_ex evals m_si fc@(FuncCall { funcName = n, arguments = ars })
    | Just si <-  M.lookup n m_si
    , Just (ev_i, _) <- HM.lookup fc (pre_evals evals) =
        let
            smt_ars = map exprToSMT $ concatMap (adjustArgs meas_ex) ars

            sy_body = foldr (\psi e ->
                                let
                                    p_ars = take (length $ sy_args psi) smt_ars
                                in
                                Func (sy_name psi) p_ars :&& e) (VBool True) (s_syn_pre si)
            fixed_body = Func (s_known_pre_name si) [VInt ev_i]
        in
        case s_status si of
                Synth -> fixed_body :&& sy_body
                Known -> fixed_body
    | otherwise = error "mkPreCall: specification not found"

mkPostCall :: MeasureExs -> Evals (Integer, Bool) -> M.Map Name SpecInfo -> FuncCall -> SMTAST
mkPostCall meas_ex evals m_si fc@(FuncCall { funcName = n, arguments = ars, returns = r })
    | Just si <-  M.lookup n m_si
    , Just (ev_i, _) <- HM.lookup fc (post_evals evals) =
        let
            smt_ars = map exprToSMT . concatMap (adjustArgs meas_ex) $ ars -- map exprToSMT . concatMap (adjustArgs meas_ex) $ ars ++ [r]
            smt_ret = extractExprPolyBoundWithRoot r

            sy_body = foldr (.&&.) (VBool True)
                    . concatMap
                        (\(syn_p, r) ->
                            let
                                smt_r = map (map exprToSMT) . map (adjustArgs meas_ex) $ r
                            in
                            map (\smt_r' -> Func (sy_name syn_p) $ smt_ars ++ smt_r') smt_r)
                    . extractValues 
                    $ zipPB (s_syn_post si) smt_ret-- Func (sy_name $ s_syn_post si) smt_ars
            fixed_body = Func (s_known_post_name si) [VInt ev_i]
        in
        case s_status si of
                Synth -> fixed_body :&& sy_body
                Known -> fixed_body
    | otherwise = error "mkPostCall: specification not found"

constraintsToSMT :: MeasureExs -> Evals (Integer, Bool)  -> M.Map Name SpecInfo -> FuncConstraints -> [SMTHeader]
constraintsToSMT meas_ex evals si =  map Solver.Assert . map (constraintToSMT meas_ex evals si) . toListFC

constraintToSMT :: MeasureExs -> Evals (Integer, Bool)  -> M.Map Name SpecInfo -> FuncConstraint -> SMTAST
constraintToSMT meas_ex evals si (Call All fc) =
    case M.lookup (funcName fc) si of
        Just si' ->
            let
                pre = mkPreCall meas_ex evals si fc
                post = mkPostCall meas_ex evals si fc
            in
            pre :=> post
        Nothing -> error "constraintToSMT: specification not found"
constraintToSMT meas_ex evals si (Call Pre fc) =
    case M.lookup (funcName fc) si of
        Just si' ->
            mkPreCall meas_ex evals si fc
        Nothing -> error $ "constraintToSMT: specification not found" ++ show fc
constraintToSMT meas_ex evals si (Call Post fc) =
    case M.lookup (funcName fc) si of
        Just si' -> mkPostCall meas_ex evals si fc
        Nothing -> error "constraintToSMT: specification not found"
constraintToSMT meas_ex evals si (AndFC fs) = mkSMTAnd $ map (constraintToSMT meas_ex evals si) fs
constraintToSMT meas_ex evals si (OrFC fs) = mkSMTOr $ map (constraintToSMT meas_ex evals si) fs
constraintToSMT meas_ex evals si (ImpliesFC fc1 fc2) = constraintToSMT meas_ex evals si fc1 :=> constraintToSMT meas_ex evals si fc2
constraintToSMT meas_ex evals si (NotFC fc) = (:!) (constraintToSMT meas_ex evals si fc)

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
envToSMT :: MeasureExs -> Evals (Integer, Bool)  -> M.Map Name SpecInfo -> FuncConstraints -> [SMTHeader]
envToSMT meas_ex evals si =
     map Solver.Assert
   . concatMap (uncurry (envToSMT' meas_ex evals si))
   . flip zip ["f" ++ show i | i <-[1..]]
   . L.nub
   . concatMap allCalls
   . toListFC

envToSMT' :: MeasureExs -> Evals (Integer, Bool)  -> M.Map Name SpecInfo -> FuncCall -> SMTName -> [SMTAST]
envToSMT' meas_ex (Evals {pre_evals = pre_ev, post_evals = post_ev}) m_si fc@(FuncCall { funcName = f }) uc_n =
    case M.lookup f m_si of
        Just si ->
            let
                (pre_i, pre_res) = case HM.lookup fc pre_ev of
                                        Just b -> b
                                        Nothing -> error "envToSMT': pre not found"

                (post_i, post_res) = case HM.lookup fc post_ev of
                                        Just b -> b
                                        Nothing -> error "envToSMT': post not found"

                pre = (if pre_res then id else (:!)) $ Func (s_known_pre_name si) [VInt pre_i]
                post = (if post_res then id else (:!)) $ Func (s_known_post_name si) [VInt post_i]
            in
            [Named pre ("pre_" ++ uc_n), Named post ("post_" ++ uc_n)]
        Nothing -> error "envToSMT': function not found"

maxCoeffConstraints :: M.Map Name SpecInfo -> [SMTHeader]
maxCoeffConstraints =
      map Solver.Assert
    . concatMap
        (\si ->
            let
                cffs = concat . concat $ allPreCoeffs si ++ allPostCoeffs si
            in
            if s_status si == Synth
                then map (\c -> (Neg (VInt (s_max_coeff si)) :<= V c SortInt)
                                    :&& (V c SortInt :<= VInt (s_max_coeff si))) cffs
                else []) . M.elems

nonMaxCoeffConstraints :: MeasureExs -> Evals (Integer, Bool)  -> M.Map Name SpecInfo -> FuncConstraints -> [SMTHeader]
nonMaxCoeffConstraints meas_ex evals m_si fc =
    let
        all_coeffs = getCoeffs m_si

        var_decl_hdrs = map (flip VarDecl SortInt) all_coeffs
        def_funs = concatMap defineLIAFuns $ M.elems m_si
        fc_smt = constraintsToSMT meas_ex evals m_si fc
        env_smt = envToSMT meas_ex evals m_si fc
    in
    var_decl_hdrs ++ def_funs ++ fc_smt ++ env_smt

getCoeffs :: M.Map Name SpecInfo -> [SMTName]
getCoeffs m_si =
    let
        all_precoeffs = gc allPreCoeffs $ M.elems m_si
        all_postcoeffs = gc allPostCoeffs $ M.elems m_si
    in
    all_precoeffs ++ all_postcoeffs
    where
        gc f = concat . concat . concatMap f . filter (\si -> s_status si == Synth)

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
            ++ map defineSynthLIAFuncSF (s_syn_pre si)
        else [])
    ++
    [ defineFixedLIAFuncSF (s_known_pre si)
    , defineFixedLIAFuncSF (s_known_post si)]

defineFixedLIAFuncSF :: FixedSpec -> SMTHeader
defineFixedLIAFuncSF fs =
    DeclareFun (fs_name fs) [SortInt] SortBool

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
buildLIA_LH :: SpecInfo -> SMTModel -> [PolyBound LHF.Expr]
buildLIA_LH si mv =
    let
        build = buildLIA ePlus eTimes bGeq PAnd POr detVar (ECon . I) -- todo: Probably want to replace PAnd with id to group?
        pre = map (\psi -> build (sy_coeffs psi) (map smt_var (sy_args psi))) (s_syn_pre si)
        post = mapPB (\psi -> build (sy_coeffs psi) (map smt_var (sy_args psi))) $ s_syn_post si
    in
    map (flip PolyBound []) pre ++ [post]
    where
        detVar v 
            | Just (VInt c) <- M.lookup v mv = ECon (I c)
            | Just sa <- L.find (\sa_ -> v == smt_var sa_) all_args = lh_rep sa
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

        all_args = allPreSpecArgs si ++ allPostSpecArgs si


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
        (ars_pb, ret_pb) = argsAndRetFromSpec ghci meas [] aty rty fspec

        ret = headValue ret_pb

        ars = map headValue ars_pb

        arg_ns = map (\(a, i) -> a { smt_var = "x_" ++ show i } ) $ zip (concat ars) [1..]
        ret_ns = map (\(r, i) -> r { smt_var = "x_r_" ++ show i }) $ zip ret [1..]
    in
    SI { s_known_pre = FixedSpec { fs_name = smt_f ++ "_known_pre"
                                 , fs_args = arg_ns }
       , s_known_post = FixedSpec { fs_name = smt_f ++ "_known_post"
                                  , fs_args = arg_ns ++ ret_ns }
       , s_syn_pre = map (\(ars', i) ->
                            SynthSpec { sy_name = smt_f ++ "_synth_pre_" ++ show i
                                      , sy_args = map (\(a, j) -> a { smt_var = "x_" ++ show j}) $ zip ars' [1..]
                                      , sy_coeffs = [] 
                                      }
                     ) $ zip ars [1..]
       , s_syn_post = mkSynSpecPB (smt_f ++ "_synth_post_") arg_ns ret_pb
       , s_status = stat }

argsAndRetFromSpec :: [GhcInfo] -> Measures -> [PolyBound [SpecArg]] -> [Type] -> Type -> SpecType -> ([PolyBound [SpecArg]], PolyBound [SpecArg])
argsAndRetFromSpec ghci meas ars (_:ts) rty (RAllT { rt_ty = out }) =
    argsAndRetFromSpec ghci meas ars ts rty out
argsAndRetFromSpec ghci meas ars (t:ts) rty rfun@(RFun { rt_bind = b, rt_in = i, rt_out = out}) =
    let
        sa = mkSpecArgPB ghci meas t rfun
    in
    case i of
        RFun {} -> argsAndRetFromSpec ghci meas ars ts rty out
        _ -> argsAndRetFromSpec ghci meas (sa:ars) ts rty out
argsAndRetFromSpec ghci meas ars _ rty rapp@(RApp { rt_reft = ref}) =
    let
        sa = mkSpecArgPB ghci meas rty rapp
    in
    (reverse ars, sa)
argsAndRetFromSpec ghci meas ars _ rty rvar@(RVar { rt_reft = ref}) =
    let
        sa = mkSpecArgPB ghci meas rty rvar
    in
    (reverse ars, sa)

mkSpecArgPB :: [GhcInfo] -> Measures -> Type -> SpecType -> PolyBound [SpecArg]
mkSpecArgPB ghci meas t st =
    let
        t_pb = extractTypePolyBound t

        sy_pb = specTypeSymbolPB st
    in
    mapPB (uncurry (mkSpecArg ghci meas)) $ zipPB sy_pb t_pb

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


mkSynSpecPB :: String -> [SpecArg] -> PolyBound [SpecArg] -> PolyBound SynthSpec
mkSynSpecPB smt_f arg_ns pb_sa =
    mapPB (\(ui, sa) ->
            let
                ret_ns = map (\(r, i) -> r { smt_var = "x_r_" ++ show ui ++ "_" ++ show i }) $ zip sa [1..]
            in
            SynthSpec { sy_name = smt_f ++ show ui
                      , sy_args = arg_ns ++ ret_ns
                      , sy_coeffs = [] }
        )
        $ zipPB (uniqueIds pb_sa) pb_sa

-- ret_ns = map (\(r, i) -> r { smt_var = "x_r_" ++ show i }) $ zip ret [1..]
       -- , s_syn_post = SynthSpec { sy_name = smt_f ++ "_synth_post"
       --                          , sy_args = arg_ns ++ ret_ns
       --                          , sy_coeffs = [] }


----------------------------------------------------------------------------
-- Manipulate SpecTypes
----------------------------------------------------------------------------

specTypeSymbol :: SpecType -> LH.Symbol
specTypeSymbol (RFun { rt_bind = b }) = b
specTypeSymbol rapp@(RApp { rt_reft = ref }) = reftSymbol $ ur_reft ref
specTypeSymbol (RVar { rt_reft = ref }) = reftSymbol $ ur_reft ref
specTypeSymbol _ = error $ "specTypeSymbol: SpecType not handled"

specTypeSymbolPB :: SpecType -> PolyBound LH.Symbol
specTypeSymbolPB rfun@(RFun { rt_bind = b, rt_in = i, rt_out = out}) =
    case specTypeSymbolPB i of
        PolyBound _ ps -> PolyBound b ps
specTypeSymbolPB (RApp { rt_reft = ref, rt_args = ars }) =
    PolyBound (reftSymbol $ ur_reft ref) $ map specTypeSymbolPB ars
specTypeSymbolPB (RVar {rt_reft = ref}) = PolyBound (reftSymbol $ ur_reft ref) []
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

allPostCoeffs :: SpecInfo -> CNF
allPostCoeffs = concatMap sy_coeffs . extractValues . s_syn_post

allPostSpecArgs :: SpecInfo -> [SpecArg]
allPostSpecArgs = concatMap sy_args . extractValues . s_syn_post
