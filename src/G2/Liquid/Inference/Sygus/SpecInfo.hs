{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.Sygus.SpecInfo where

import G2.Language as G2
import qualified G2.Language.ExprEnv as E
import G2.Liquid.Conversion
import G2.Liquid.Helpers
import G2.Liquid.Types hiding (SP)
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.FuncConstraint
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.GeneratedSpecs
import G2.Liquid.Inference.PolyRef
import G2.Liquid.Inference.UnionPoly
import G2.Solver as Solver

import Language.Haskell.Liquid.Types as LH hiding (SP, ms, isBool)
import Language.Fixpoint.Types.Refinements as LH hiding (pAnd, pOr)
import qualified Language.Fixpoint.Types as LH

import Control.Monad
import qualified Control.Monad.State.Lazy as SM
import Data.Coerce
import qualified Data.HashMap.Lazy as HM
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T
import Data.Semigroup (Semigroup (..))


type NMExprEnv = HM.HashMap (T.Text, Maybe T.Text) G2.Expr

-- A list of functions that still must have specifications synthesized at a lower level
type ToBeNames = [Name]

-- A list of functions to synthesize a the current level
type ToSynthNames = [Name]

data Forms = LIA { -- LIA formulas
                   c_active :: SMTName

                 , c_op_branch1 :: SMTName
                 , c_op_branch2 :: SMTName
                 , c_op_branch3 :: SMTName

                 , b0 :: SMTName

                 -- Argument and return value coefficients for the LHS of an operator.
                 , ars_coeffs :: [SMTName]
                 , rets_coeffs :: [SMTName]
                 
                 -- Argument and return value coefficients for the RHS of an operator- only used with mod.
                 , ars_coeffs_rhs :: [SMTName]
                 , rets_coeffs_rhs :: [SMTName]
                 
                 , allow_mod :: UseMod }
           | Set { c_active :: SMTName
                 , c_op_branch1 :: SMTName
                 , c_op_branch2 :: SMTName
                 , c_op_branch3 :: SMTName

                 , int_sing_set_bools_lhs :: [[SMTName]]
                 , int_sing_set_bools_rhs :: [[SMTName]]

                 , ars_bools_lhs :: [[SMTName]]
                 , rets_bools_lhs :: [[SMTName]]

                 , ars_bools_rhs :: [[SMTName]]
                 , rets_bools_rhs :: [[SMTName]]
                 }
           | BoolForm { c_active :: SMTName
                      , c_op_branch1 :: SMTName
                      , c_op_branch2 :: SMTName
                      , c_op_branch3 :: SMTName

                      , ars_bools :: [SMTName]
                      , rets_bools :: [SMTName]

                      , forms :: [Forms]
                      }
                 deriving Show

coeffs :: Forms -> [SMTName]
coeffs cf@(LIA {}) = b0 cf:ars_coeffs cf ++ rets_coeffs cf ++ ars_coeffs_rhs cf ++ rets_coeffs_rhs cf
coeffs (Set {}) = []
coeffs cf@(BoolForm {}) = concatMap coeffs (forms cf)

coeffsNoB :: Forms -> [SMTName]
coeffsNoB cf@(LIA {}) = ars_coeffs cf ++ rets_coeffs cf  ++ ars_coeffs_rhs cf ++ rets_coeffs_rhs cf
coeffsNoB (Set {}) = []
coeffsNoB cf@(BoolForm {}) = concatMap coeffsNoB (forms cf)

setBools :: Forms -> [SMTName]
setBools (LIA {}) = []
setBools s@(Set {}) =
    concat $ int_sing_set_bools_lhs s ++ int_sing_set_bools_rhs s ++ ars_bools_lhs s ++ rets_bools_lhs s ++ ars_bools_rhs s ++ rets_bools_rhs s
setBools cf@(BoolForm {}) = concatMap setBools (forms cf)

boolBools :: Forms -> [SMTName]
boolBools (LIA {}) = []
boolBools (Set {}) = []
boolBools cf@(BoolForm {}) = ars_bools cf ++ rets_bools cf ++ concatMap boolBools (forms cf)


type Clause = (SMTName, [Forms])
type CNF = [Clause]

data SpecInfo = SI { s_max_coeff :: Integer

                   -- A function that is used to record the value of the function at known points,
                   -- i.e. points that occur in the FuncConstraints
                   , s_known_pre :: FixedSpec
                   , s_known_post :: FixedSpec

                   -- A function specification that must be synthesized in the future, at a lower level
                   , s_to_be_pre :: ToBeSpec
                   , s_to_be_post :: ToBeSpec

                   -- Functions that capture the pre and post condition.
                   -- We have one precondition function per argument
                   , s_syn_pre :: [PolyBound SynthSpec]
                   , s_syn_post :: PolyBound SynthSpec

                   , s_type_pre :: [Type]
                   , s_type_post :: Type

                   , s_status :: Status }
                   deriving (Show)

s_known_pre_name :: SpecInfo -> SMTName
s_known_pre_name = fs_name . s_known_pre

s_known_post_name :: SpecInfo -> SMTName
s_known_post_name = fs_name . s_known_post

s_to_be_pre_name :: SpecInfo -> SMTName
s_to_be_pre_name = tb_name . s_to_be_pre

s_to_be_post_name :: SpecInfo -> SMTName
s_to_be_post_name = tb_name . s_to_be_post

data FixedSpec = FixedSpec { fs_name :: SMTName
                           , fs_args :: [SpecArg] }
                           deriving (Show)

data ToBeSpec = ToBeSpec { tb_name :: SMTName
                         , tb_args :: [SpecArg] }
                         deriving (Show)

data SynthSpec = SynthSpec { sy_name :: SMTName
                           , sy_args :: [SpecArg]
                           , sy_rets :: [SpecArg]
                           , sy_coeffs :: CNF }
                           deriving (Show)

sy_args_and_ret :: SynthSpec -> [SpecArg]
sy_args_and_ret si = sy_args si ++ sy_rets si

int_sy_args :: SynthSpec -> [SpecArg]
int_sy_args = filter (\a -> smt_sort a == SortInt) . sy_args

int_sy_rets :: SynthSpec -> [SpecArg]
int_sy_rets = filter (\a -> smt_sort a == SortInt) . sy_rets

set_sy_args :: SynthSpec -> [SpecArg]
set_sy_args = filter (isSet . smt_sort) . sy_args

set_sy_rets :: SynthSpec -> [SpecArg]
set_sy_rets = filter (isSet . smt_sort) . sy_rets

bool_sy_args :: SynthSpec -> [SpecArg]
bool_sy_args = filter (\a -> smt_sort a == SortBool) . sy_args

bool_sy_rets :: SynthSpec -> [SpecArg]
bool_sy_rets = filter (\a -> smt_sort a == SortBool) . sy_rets

isSet :: Sort -> Bool
isSet (SortArray _ _) = True
isSet _ = False

int_sy_args_and_ret :: SynthSpec -> [SpecArg]
int_sy_args_and_ret si = int_sy_args si ++ int_sy_rets si

set_sy_args_and_ret :: SynthSpec -> [SpecArg]
set_sy_args_and_ret si = set_sy_args si ++ set_sy_rets si

bool_sy_args_and_ret :: SynthSpec -> [SpecArg]
bool_sy_args_and_ret si = bool_sy_args si ++ bool_sy_rets si

all_sy_args_and_ret :: SynthSpec -> [SpecArg]
all_sy_args_and_ret si = int_sy_args_and_ret si ++ set_sy_args_and_ret si ++ bool_sy_args_and_ret si

data SpecArg = SpecArg { lh_rep :: LH.Expr
                       , smt_var :: SMTName
                       , smt_sort :: Sort}
                       deriving (Show)

data Status = Synth -- ^ A specification should be synthesized
            | ToBeSynthed -- ^ The specification will be synthesized at some lower level
            | Known -- ^ The specification is completely fixed
            deriving (Eq, Show)

buildNMExprEnv :: ExprEnv -> NMExprEnv
buildNMExprEnv = HM.fromList . map (\(n, e) -> ((nameOcc n, nameModule n), e)) . E.toExprList

buildSpecInfo :: (InfConfigM m, ProgresserM m) =>
                 NMExprEnv
              -> TypeEnv
              -> TypeClasses
              -> Measures
              -> [GhcInfo]
              -> FuncConstraints
              -> UnionedTypes
              -> ToBeNames
              -> ToSynthNames
              -> m (M.Map Name SpecInfo)
buildSpecInfo eenv tenv tc meas ghci fc ut to_be_ns ns_synth = do
    -- Compensate for zeroed out names in FuncConstraints
    let ns_synth' = map zeroOutName ns_synth

    -- Figure out what the other functions relevant to the current spec are
    let all_calls = concatMap allCallNames $ toListFC fc
        non_ns = filter (`notElem` ns_synth') all_calls

    -- Form tuples of:
    -- (1) Func Names
    -- (2) Function Argument Types
    -- (3) Function Known Types
    -- to be used in forming SpecInfo's
    let ns_aty_rty = map (relNameTypePairs eenv) ns_synth'

        other_aty_rty = map (relNameTypePairs eenv) non_ns
        to_be_ns' = map zeroOutName to_be_ns
        (to_be_ns_aty_rty, known_ns_aty_rty) = L.partition (\(n, _) -> n `elem` to_be_ns') other_aty_rty


    si <- foldM (\m (n, (at, rt)) -> do
        s <- buildSI tenv tc meas ut Synth ghci n at rt
        return $ M.insert n s m) M.empty ns_aty_rty
    si' <- foldM (\m (n, (at, rt)) -> do
        s <- buildSI tenv tc meas ut ToBeSynthed ghci n at rt
        return $ M.insert n s m) si to_be_ns_aty_rty
    si'' <- foldM (\m (n, (at, rt)) -> do
        s <- buildSI tenv tc meas ut Known ghci n at rt
        return $ M.insert n s m) si' known_ns_aty_rty

    inf_con <- infConfigM

    let si''' = if use_invs inf_con
                    then allCondsKnown . conflateLoopNames . elimSyArgs $ si''
                    else si''

    return si'''
    where
      zeroOutName (Name n m _ l) = Name n m 0 l

relNameTypePairs :: NMExprEnv -> Name -> (Name, ([Type], Type))
relNameTypePairs eenv n =
    case HM.lookup (nameOcc n, nameModule n) eenv of
        Just e' -> (n, generateRelTypesFromExpr e')
        Nothing -> error $ "synthesize: No expr found"

generateRelTypesFromExpr :: G2.Expr -> ([Type], Type)
generateRelTypesFromExpr = generateRelTypes . inTyForAlls . typeOf

generateRelTypes :: Type -> ([Type], Type)
generateRelTypes t =
    let
        ty_e = PresType t
        arg_ty_c = filter (not . isTYPE)
                 . filter (notLH)
                 $ argumentTypes ty_e
        ret_ty_c = returnType ty_e
    in
    (arg_ty_c, ret_ty_c)

------------------------------------
-- Building SpecInfos
------------------------------------

buildSI :: (InfConfigM m, ProgresserM m) => TypeEnv -> TypeClasses -> Measures -> UnionedTypes -> Status -> [GhcInfo] ->  Name -> [Type] -> Type -> m SpecInfo
buildSI tenv tc meas uts stat ghci f aty rty = do
    let smt_f = nameToStr f
        fspec = case genSpec ghci f of
                Just spec' -> spec'
                _ -> error $ "synthesize: No spec found for " ++ show f

    let ut = case lookupUT f uts of
                    Just _ut -> _ut
                    Nothing -> error $ "buildSI: Missing UnionedType " ++ show f
        (ut_a, ut_r) = generateRelTypes ut
        ut_a_r = reverse . take (length aty) $ reverse ut_a
        -- ut_a' = reverse . take (length outer_ars_pb) $ reverse ut_a
    (outer_ars_pb, ut_a', ret_pb) <- argsAndRetFromSpec tenv tc ghci meas [] [] aty rty ut_a_r fspec
    let outer_ars = map fst outer_ars_pb
        ret_v = headValue ret_pb

        arg_ns = zipWith (\a i -> a { smt_var = "x_" ++ show i } ) (concat outer_ars) ([1..] :: [Integer])
        ret_ns = zipWith (\r i -> r { smt_var = "x_r_" ++ show i }) (aar_r ret_v) ([1..] :: [Integer])

    let -- smt_names = assignNamesAndArgCount ut
        smt_names = assignNamesAndArgCount $ mkTyFun (ut_a' ++ [ut_r])

        pre_specs =
            zipWith3 (\ars_pb ut_ar i ->
                        let
                            ut_pb = extractTypeAppAndFuncPolyBound ut_ar

                            ars = map fst (init ars_pb)
                            r_pb = snd (last ars_pb)
                        in
                        mapPB (\(AAndR { aar_a = ex_a, aar_r = rets }, t, j) ->
                            case unTyApp t of
                                TyVar (Id ut_n _):_ ->
                                    let
                                        (nme, count) = fromMaybe
                                            ("_synth_pre_filler_" ++ show i ++ "_" ++ show j, 0)
                                            (HM.lookup ut_n smt_names)
                                    in
                                    SynthSpec { sy_name = smt_f ++ "_spec" ++ nme
                                                , sy_args = zipWith (\a k -> a { smt_var = "x_" ++ show k}) (concat (take count ars) ++ ex_a) ([1..] :: [Integer])
                                                , sy_rets = zipWith (\r k -> r { smt_var = "x_r_" ++ show k}) rets ([1..] :: [Integer])
                                                , sy_coeffs = []}
                                TyFun _ _:_ ->
                                        SynthSpec { sy_name = smt_f ++ "_synth_pre_filler_" ++ show i ++ "_" ++ show j
                                                , sy_args = []
                                                , sy_rets = []
                                                , sy_coeffs = []}
                                _ -> error "buildSI: unsupported Type"
                                )  $ zip3PB r_pb ut_pb (uniqueIds r_pb)
                    ) (filter (not . null) $ L.inits outer_ars_pb) ut_a' ([1..] :: [Integer])

    return
        SI { s_max_coeff = 0
           , s_known_pre = FixedSpec { fs_name = smt_f ++ "_known_pre"
                                     , fs_args = arg_ns }
           , s_known_post = FixedSpec { fs_name = smt_f ++ "_known_post"
                                      , fs_args = arg_ns ++ ret_ns }
           , s_to_be_pre = ToBeSpec { tb_name = smt_f ++ "_to_be_pre"
                                    , tb_args = arg_ns }
           , s_to_be_post = ToBeSpec { tb_name = smt_f ++ "_to_be_post"
                                     , tb_args = arg_ns ++ ret_ns }
           , s_syn_pre = pre_specs
           , s_syn_post = mkSynSpecPB smt_f outer_ars (mapPB aar_r ret_pb) smt_names ut_r

           , s_type_pre = aty
           , s_type_post = rty

           , s_status = stat }

data ArgsAndRet = AAndR { aar_a :: [SpecArg], aar_r :: [SpecArg] } deriving Show

instance Semigroup ArgsAndRet where
    AAndR { aar_a = a1, aar_r = r1 } <> AAndR { aar_a = a2, aar_r = r2 } = AAndR { aar_a = a1 <> a2, aar_r = r1 <> r2 }

instance Monoid ArgsAndRet where
    mempty = AAndR { aar_a = [], aar_r = [] }

argsAndRetFromSpec :: (InfConfigM m, ProgresserM m) => TypeEnv -> TypeClasses -> [GhcInfo] -> Measures -> [([SpecArg], PolyBound ArgsAndRet)] -> [Type] -> [Type] -> Type -> [Type] -> SpecType
                                                    -> m ([([SpecArg], PolyBound ArgsAndRet)], [Type], PolyBound ArgsAndRet)
argsAndRetFromSpec tenv tc ghci meas ars u_ars ts rty us (RAllT { rt_ty = out }) =
    argsAndRetFromSpec tenv tc ghci meas ars u_ars ts rty us out
argsAndRetFromSpec tenv tc ghci meas ars u_ars (t:ts) rty (u:us) (RFun { rt_in = rfun@(RFun {}), rt_out = out}) = do
    let (ts', rty') = generateRelTypes t
    (f_ars, _, f_ret) <- argsAndRetFromSpec tenv tc ghci meas ars u_ars ts' rty' (argumentTypes $ PresType u) rfun
    let f_ret_list = case f_ret of
                        PolyBound (AAndR { aar_a = [], aar_r = [] }) [] -> []
                        _ -> [f_ret]
        f_ars_sa = map fst f_ars
        f_ars' = zipWith (\sa pb -> mapPB (AAndR (concat sa)) pb) (L.inits f_ars_sa) (map (mapPB aar_r) $ map snd f_ars ++ f_ret_list)
    argsAndRetFromSpec tenv tc ghci meas (([], PolyBound mempty f_ars'):ars) (u:u_ars) ts rty us out
argsAndRetFromSpec tenv tc ghci meas ars u_ars (t:ts) rty (u:us) rfun@(RFun { rt_in = i, rt_out = out}) = do
    (m_out_symb, sa) <- mkSpecArgPB ghci tenv meas t rfun
    let out_symb = case m_out_symb of
                      Just os -> os
                      Nothing -> error "argsAndRetFromSpec: out_symb is Nothing"
    case i of
        RVar {} -> argsAndRetFromSpec tenv tc ghci meas ars u_ars ts rty us out
        RFun {} -> argsAndRetFromSpec tenv tc ghci meas ars u_ars ts rty us out
        _ -> argsAndRetFromSpec tenv tc ghci meas ((out_symb, sa):ars) (u:u_ars) ts rty us out
argsAndRetFromSpec tenv _ ghci meas ars u_ars _ rty uts rapp@(RApp {}) = do
    (_, sa) <- mkSpecArgPB ghci tenv meas rty rapp
    return (reverse ars, reverse u_ars, sa)
argsAndRetFromSpec tenv _ ghci meas ars u_ars _ rty uts rvar@(RVar {}) = do
    (_, sa) <- mkSpecArgPB ghci tenv meas rty rvar
    return (reverse ars, reverse u_ars, sa)
argsAndRetFromSpec _ _ _ _ _ _ [] _ _ st@(RFun {}) = error $ "argsAndRetFromSpec: RFun with empty type list " ++ show st
argsAndRetFromSpec _ _ _ _ _ _ _ _ us st = error $ "argsAndRetFromSpec: unhandled SpecType " ++ show st ++ "\n" ++ show us

mkSpecArgPB :: (InfConfigM m, ProgresserM m) => [GhcInfo] -> TypeEnv -> Measures -> Type -> SpecType -> m (Maybe [SpecArg], PolyBound ArgsAndRet)
mkSpecArgPB ghci tenv meas t st = do
    MaxSize mx_meas <- maxSynthFormSizeM
    let t_pb = extractTypePolyBound t

        sy_pb = specTypeSymbolPB st
        in_sy_pb = mapPB inner sy_pb

        t_sy_pb = filterPBByType snd $ zipPB in_sy_pb t_pb
        t_sy_pb' = case t_sy_pb of
                    Just pb -> pb
                    Nothing -> PolyBound (inner $ headValue sy_pb, t) []

        out_symb = outer $ headValue sy_pb
        out_spec_arg = fmap (\os -> mkSpecArg (fromInteger mx_meas) ghci tenv meas os t) out_symb

    return (out_spec_arg, mapPB (ret . uncurry (mkSpecArg (fromInteger mx_meas) ghci tenv meas)) t_sy_pb')


mkSpecArg :: Int -> [GhcInfo] -> TypeEnv -> Measures -> LH.Symbol -> Type -> [SpecArg]
mkSpecArg mx_meas ghci tenv meas symb t =
    let
        srt = typeToSort t
    in
    case srt of
        Just srt' ->
            [SpecArg { lh_rep = EVar symb
                     , smt_var = "tbd"
                     , smt_sort = srt' }]
        Nothing ->
            let
                app_meas = applicableMeasuresType mx_meas tenv meas t
                app_meas' = L.sortBy (\(n1, _) (n2, _) -> compare n1 n2) app_meas
            in
            mapMaybe
                (\(mn, (at, rt)) ->
                    let vm = t `specializes` at in
                    case vm of
                        Just vm' ->
                            let

                                rt' = applyTypeMap vm' rt
                            in
                            fmap (\srt' ->
                                    let
                                        lh_mn = map (getLHMeasureName ghci) mn
                                    in
                                    SpecArg { lh_rep = foldr EApp (EVar symb) $ map EVar lh_mn
                                            , smt_var = "tbd"
                                            , smt_sort = srt'}) $ typeToSort rt'
                        Nothing -> Nothing) app_meas'

ret :: [SpecArg] -> ArgsAndRet
ret sa = AAndR { aar_a = [], aar_r = sa }

mkSynSpecPB :: String -> [[SpecArg]] -> PolyBound [SpecArg] -> HM.HashMap Name (SMTName, Int) -> Type -> PolyBound SynthSpec
mkSynSpecPB smt_f ars pb_sa smt_names ut =
    let
        ut_pb = extractTypePolyBound ut
    in
    mapPB (\(sa, t, ui) ->
            let
                TyVar (Id ut_n _):_ = unTyApp t
                (nme, count) = fromMaybe
                    ("_synth_post_filler", 0)
                    (HM.lookup ut_n smt_names)
                arg_ns = zipWith (\a i -> a { smt_var = "x_" ++ show i } ) (concat . take count $ ars) ([1..] :: [Integer])
                ret_ns = map (\(r, i) -> r { smt_var = "x_r_" ++ show ui ++ "_" ++ show i }) $ zip sa ([1..] :: [Integer])
            in
            SynthSpec { sy_name = smt_f ++ "_spec" ++ nme -- smt_f ++ show ui
                      , sy_args = arg_ns
                      , sy_rets = ret_ns
                      , sy_coeffs = [] }
        )
        $ zip3PB pb_sa ut_pb (uniqueIds pb_sa)

filterPBByType :: (v -> Type) -> PolyBound v -> Maybe (PolyBound v)
filterPBByType f = filterPB (\(PolyBound v _) ->
                                let
                                    t = f v
                                in
                                not (isTyVar t))

assignNamesAndArgCount :: Type -> HM.HashMap Name (SMTName, Int)
assignNamesAndArgCount t = SM.evalState (assignNamesAndArgCount' 0 HM.empty t) 0

assignNamesAndArgCount' :: Int -> HM.HashMap Name (SMTName, Int) -> Type -> SM.State Int (HM.HashMap Name (SMTName, Int))
assignNamesAndArgCount' ar_count hm (TyVar (Id n k))
    | Nothing <- HM.lookup n hm = do
        pos <- SM.get
        SM.modify' (+ 1)
        return $ HM.insert n ("_synth_" ++ show ar_count ++ "_" ++ show pos, ar_count) hm
    | otherwise = return hm
assignNamesAndArgCount' ar_count hm (TyFun t1 t2) = do
    hm' <- assignNamesAndArgCount' ar_count hm t1
    assignNamesAndArgCount' (ar_count + 1) hm' t2
assignNamesAndArgCount' ar_count hm (TyApp t1 t2) = do
    hm' <- assignNamesAndArgCount' ar_count hm t1
    assignNamesAndArgCount' ar_count hm' t2
assignNamesAndArgCount' ar_count hm (TyForAll _ t) = assignNamesAndArgCount' ar_count hm t
assignNamesAndArgCount' _ hm _ = return hm

----------------------------------------------------------------------------
-- Manipulate Evals
----------------------------------------------------------------------------

-- We assign a unique id to each function call, and use these as the arguments
-- to the known functions, rather than somehow using the arguments directly.
-- This means we can get away with needing only a single known function
-- for the pre, and a single known function for the post, as opposed
-- to needing individual known functions/function calls for polymorphic refinements.
assignIds :: Evals Bool -> Evals (Integer, Bool)
assignIds = snd . mapAccumLEvals (\i b -> (i + 1, (i, b))) 0

----------------------------------------------------------------------------
-- Manipulate SpecTypes
----------------------------------------------------------------------------

data SymbolPair = SP { inner :: LH.Symbol, outer :: Maybe LH.Symbol }

specTypeSymbolPB :: SpecType -> PolyBound SymbolPair
specTypeSymbolPB (RFun { rt_bind = b, rt_in = i }) =
    case specTypeSymbolPB i of
        PolyBound sp ps -> PolyBound (sp { outer = Just b}) ps
specTypeSymbolPB (RApp { rt_reft = ref, rt_args = ars }) =
    PolyBound (SP { inner = reftSymbol $ ur_reft ref, outer = Nothing}) $ map specTypeSymbolPB ars
specTypeSymbolPB (RVar {rt_reft = ref}) =
    PolyBound (SP { inner = reftSymbol $ ur_reft ref, outer = Nothing }) []
specTypeSymbolPB r = error $ "specTypeSymbolPB: Unexpected SpecType" ++ "\n" ++ show r

reftSymbol :: Reft -> LH.Symbol
reftSymbol = fst . unpackReft

unpackReft :: Reft -> (LH.Symbol, LH.Expr)
unpackReft = coerce

----------------------------------------------------------------------------
-- Invariant configuration
----------------------------------------------------------------------------

elimPolyArgSpecs :: M.Map a SpecInfo -> M.Map a SpecInfo
elimPolyArgSpecs = M.map elimPolyArgSpecs'

elimPolyArgSpecs' :: SpecInfo -> SpecInfo
elimPolyArgSpecs' si = si { s_syn_pre = map (\(PolyBound a _) -> PolyBound a []) (s_syn_pre si)
                          , s_syn_post = (\(PolyBound a _) -> PolyBound a []) (s_syn_post si)}

elimSyArgs :: M.Map Name SpecInfo -> M.Map Name SpecInfo
elimSyArgs = M.mapWithKey (\n si -> if specialFunction n then elimSyArgs' si else si)

elimSyArgs' :: SpecInfo -> SpecInfo
elimSyArgs' si = si { s_syn_pre = map (mapPB dropNonDirectInt) (s_syn_pre si)
                    , s_syn_post = mapPB dropNonDirectInt (s_syn_post si)}

dropNonDirectInt :: SynthSpec -> SynthSpec
dropNonDirectInt sy = sy { sy_args = filter dropNonDirectInt' (sy_args sy) }

dropNonDirectInt' :: SpecArg -> Bool
dropNonDirectInt' sy =
    case lh_rep sy of
        EVar {} -> True
        _ -> False

specialFunction :: Name -> Bool
specialFunction (Name n _ _ _) | T.take 4 n == "loop" = True
                               | T.take 5 n == "while" = True
                               | T.take 5 n == "breakWhile" = True
                               | otherwise = False

conflateLoopNames ::  M.Map a SpecInfo -> M.Map a SpecInfo
conflateLoopNames = M.map conflateLoopNames'

conflateLoopNames' :: SpecInfo -> SpecInfo
conflateLoopNames' si@(SI { s_syn_pre = pb_sy_pre@(_:_)
                          , s_syn_post = pb_post@(PolyBound sy_post _) })
    | take 4 (sy_name sy_post) == "loop" =
        let
            pb_pre = last pb_sy_pre
        in
        si { s_syn_pre = init pb_sy_pre ++ [conflateLoopNames'' pb_pre pb_post] }
conflateLoopNames' si = si

conflateLoopNames'' :: PolyBound SynthSpec -> PolyBound SynthSpec -> PolyBound SynthSpec
conflateLoopNames'' pb1 = mapPB (\(sy1, sy2) -> sy1 { sy_name = sy_name sy2} ) . zipPB pb1

allCondsKnown ::  M.Map a SpecInfo -> M.Map a SpecInfo
allCondsKnown = M.map allCondsKnown'

allCondsKnown' :: SpecInfo -> SpecInfo
allCondsKnown' si@(SI { s_syn_post = (PolyBound sy_post _) })
    | take 4 (sy_name sy_post) == "cond" = si { s_status = Known }
allCondsKnown' si = si

----------------------------------------------------------------------------

typeToSort :: Type -> Maybe Sort
typeToSort (TyApp (TyCon (Name n _ _ _) _) t)
    | n == "Set"
    , Just s <- typeToSort t = Just (SortArray s SortBool)
typeToSort (TyCon (Name n _ _ _) _)
    | n == "Int"  = Just SortInt
    | n == "Bool" = Just SortBool
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

applicableMeasuresType :: Int -> TypeEnv -> Measures -> Type -> [([Name], (Type, Type))]
applicableMeasuresType mx_meas tenv meas t =
    HM.toList . HM.map (\es -> case filter notLH . anonArgumentTypes $ last es of
                                [at]
                                  | Just (rt, _) <- chainReturnType t es -> (at, rt)
                                _ -> error $ "applicableMeasuresType: too many arguments" ++ "\n" ++ show es)
              $ applicableMeasures mx_meas tenv meas t

applicableMeasures :: Int -> TypeEnv -> Measures -> Type -> HM.HashMap [Name] [G2.Expr]
applicableMeasures mx_meas tenv meas t =
    HM.fromList . map unzip
                . filter repFstSnd
                . filter (maybe False (isJust . typeToSort . fst) . chainReturnType t . map snd)
                $ formMeasureComps mx_meas tenv t meas

-- LiquidHaskell includes measures to extract from tuples of various sizes.
-- It includes redundant pairs (fst and x_Tuple21) and (snd and x_Tuple22).
-- Including both measures slows down the synthesis, so we eliminates
-- chains involving x_Tuple21 and x_Tuple22.
repFstSnd :: [(Name, a)] -> Bool
repFstSnd = all (\(Name n _ _ _) -> n /= "x_Tuple21" && n /= "x_Tuple22") . map fst

notLH :: Type -> Bool
notLH ty
    | TyCon (Name n _ _ _) _ <- tyAppCenter ty = n /= "lh"
    | otherwise = True

