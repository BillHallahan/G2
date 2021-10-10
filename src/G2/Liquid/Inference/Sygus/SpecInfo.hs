{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.Sygus.SpecInfo where

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

import Language.Haskell.Liquid.Types as LH hiding (SP, ms, isBool)
import Language.Fixpoint.Types.Refinements as LH hiding (pAnd, pOr)
import qualified Language.Fixpoint.Types as LH

import Control.Monad
import Data.Coerce
import qualified Data.HashMap.Lazy as HM
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

type NMExprEnv = HM.HashMap (T.Text, Maybe T.Text) G2.Expr

-- A list of functions that still must have specifications synthesized at a lower level
type ToBeNames = [Name]

-- A list of functions to synthesize a the current level
type ToSynthNames = [Name]


data Forms = LIA { -- LIA formulas
                   c_active :: SMTName
               
                 , c_op_branch1 :: SMTName
                 , c_op_branch2 :: SMTName

                 , b0 :: SMTName
                 , ars_coeffs :: [SMTName]
                 , rets_coeffs :: [SMTName] }
           | Set { c_active :: SMTName
                 , c_op_branch1 :: SMTName
                 , c_op_branch2 :: SMTName

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

                      , ars_bools :: [SMTName]
                      , rets_bools :: [SMTName]

                      , forms :: [Forms]
                      }
                 deriving Show

coeffs :: Forms -> [SMTName]
coeffs cf@(LIA {}) = b0 cf:ars_coeffs cf ++ rets_coeffs cf
coeffs (Set {}) = []
coeffs cf@(BoolForm {}) = concatMap coeffs (forms cf)

coeffsNoB :: Forms -> [SMTName]
coeffsNoB cf@(LIA {}) = ars_coeffs cf ++ rets_coeffs cf
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

-- Internal Types
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
              -> ToBeNames
              -> ToSynthNames
              -> m (M.Map Name SpecInfo)
buildSpecInfo eenv tenv tc meas ghci fc to_be_ns ns_synth = do
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
        s <- buildSI tenv tc meas Synth ghci n at rt
        return $ M.insert n s m) M.empty ns_aty_rty
    si' <- foldM (\m (n, (at, rt)) -> do
        s <- buildSI tenv tc meas ToBeSynthed ghci n at rt
        return $ M.insert n s m) si to_be_ns_aty_rty
    si'' <- foldM (\m (n, (at, rt)) -> do
        s <- buildSI tenv tc meas Known ghci n at rt
        return $ M.insert n s m) si' known_ns_aty_rty

    let si''' = conflateLoopNames . elimSyArgs {- . elimPolyArgSpecs -} $ si''

    return si'''
    where
      zeroOutName (Name n m _ l) = Name n m 0 l

relNameTypePairs :: NMExprEnv -> Name -> (Name, ([Type], Type))
relNameTypePairs eenv n =
    case HM.lookup (nameOcc n, nameModule n) eenv of
        Just e' -> (n, generateRelTypes e')
        Nothing -> error $ "synthesize: No expr found"

generateRelTypes :: G2.Expr -> ([Type], Type)
generateRelTypes e =
    let
        ty_e = PresType $ inTyForAlls (typeOf e)
        arg_ty_c = filter (not . isTYPE)
                 . filter (notLH)
                 $ argumentTypes ty_e
        ret_ty_c = returnType ty_e
    in
    (arg_ty_c, ret_ty_c)

------------------------------------
-- Building SpecInfos
------------------------------------

buildSI :: (InfConfigM m, ProgresserM m) => TypeEnv -> TypeClasses -> Measures -> Status -> [GhcInfo] ->  Name -> [Type] -> Type -> m SpecInfo
buildSI tenv tc meas stat ghci f aty rty = do
    let smt_f = nameToStr f
        fspec = case genSpec ghci f of
                Just spec' -> spec'
                _ -> error $ "synthesize: No spec found for " ++ show f

    (outer_ars_pb, ret_pb) <- argsAndRetFromSpec tenv tc ghci meas [] aty rty fspec
    let outer_ars = map fst outer_ars_pb
        ret = headValue ret_pb

        arg_ns = map (\(a, i) -> a { smt_var = "x_" ++ show i } ) $ zip (concat outer_ars) ([1..] :: [Integer])
        ret_ns = map (\(r, i) -> r { smt_var = "x_r_" ++ show i }) $ zip ret ([1..] :: [Integer])

    return $ 
        SI { s_max_coeff = 0
           , s_known_pre = FixedSpec { fs_name = smt_f ++ "_known_pre"
                                     , fs_args = arg_ns }
           , s_known_post = FixedSpec { fs_name = smt_f ++ "_known_post"
                                      , fs_args = arg_ns ++ ret_ns }
           , s_to_be_pre = ToBeSpec { tb_name = smt_f ++ "_to_be_pre"
                                    , tb_args = arg_ns }
           , s_to_be_post = ToBeSpec { tb_name = smt_f ++ "_to_be_post"
                                     , tb_args = arg_ns ++ ret_ns }
           , s_syn_pre =
                map (\(ars_pb, i) ->
                            let
                                ars = concatMap fst (init ars_pb)
                                r_pb = snd (last ars_pb)
                            in
                            mapPB (\(rets, j) ->
                                    SynthSpec { sy_name = smt_f ++ "_synth_pre_" ++ show i ++ "_" ++ show j
                                              , sy_args = map (\(a, k) -> a { smt_var = "x_" ++ show k}) $ zip ars ([1..] :: [Integer])
                                              , sy_rets = map (\(r, k) -> r { smt_var = "x_r_" ++ show k}) $ zip rets ([1..] :: [Integer])
                                              , sy_coeffs = []}
                                  )  $ zipPB r_pb (uniqueIds r_pb)
                     ) $ zip (filter (not . null) $ L.inits outer_ars_pb) ([1..] :: [Integer])
           , s_syn_post = mkSynSpecPB (smt_f ++ "_synth_post_") arg_ns ret_pb

           , s_type_pre = aty
           , s_type_post = rty

           , s_status = stat }

argsAndRetFromSpec :: (InfConfigM m, ProgresserM m) => TypeEnv -> TypeClasses -> [GhcInfo] -> Measures -> [([SpecArg], PolyBound [SpecArg])] -> [Type] -> Type -> SpecType -> m ([([SpecArg], PolyBound [SpecArg])], PolyBound [SpecArg])
argsAndRetFromSpec tenv tc ghci meas ars ts rty (RAllT { rt_ty = out }) =
    argsAndRetFromSpec tenv tc ghci meas ars ts rty out
argsAndRetFromSpec tenv tc ghci meas ars (t:ts) rty rfun@(RFun { rt_in = i, rt_out = out}) = do
    (Just out_symb, sa) <- mkSpecArgPB ghci tenv meas t rfun
    case i of
        RVar {} -> argsAndRetFromSpec tenv tc ghci meas ars ts rty out
        RFun {} -> argsAndRetFromSpec tenv tc ghci meas ars ts rty out
        _ -> argsAndRetFromSpec tenv tc ghci meas ((out_symb, sa):ars) ts rty out
argsAndRetFromSpec tenv _ ghci meas ars _ rty rapp@(RApp {}) = do
    (_, sa) <- mkSpecArgPB ghci tenv meas rty rapp
    return (reverse ars, sa)
argsAndRetFromSpec tenv _ ghci meas ars _ rty rvar@(RVar {}) = do
    (_, sa) <- mkSpecArgPB ghci tenv meas rty rvar
    return (reverse ars, sa)
argsAndRetFromSpec _ _ _ _ _ [] _ st@(RFun {}) = error $ "argsAndRetFromSpec: RFun with empty type list " ++ show st
argsAndRetFromSpec _ _ _ _ _ _ _ st = error $ "argsAndRetFromSpec: unhandled SpecType " ++ show st

mkSpecArgPB :: (InfConfigM m, ProgresserM m) => [GhcInfo] -> TypeEnv -> Measures -> Type -> SpecType -> m (Maybe [SpecArg], PolyBound [SpecArg])
mkSpecArgPB ghci tenv meas t st = do
    MaxSize mx_meas <- maxSynthSizeM
    let t_pb = extractTypePolyBound t

        sy_pb = specTypeSymbolPB st
        in_sy_pb = mapPB inner sy_pb

        t_sy_pb = filterPBByType snd $ zipPB in_sy_pb t_pb
        t_sy_pb' = case t_sy_pb of
                    Just pb -> pb
                    Nothing -> PolyBound (inner $ headValue sy_pb, t) []

        out_symb = outer $ headValue sy_pb
        out_spec_arg = fmap (\os -> mkSpecArg (fromInteger mx_meas) ghci tenv meas os t) out_symb
    
    return (out_spec_arg, mapPB (uncurry (mkSpecArg (fromInteger mx_meas) ghci tenv meas)) t_sy_pb')


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
                    let
                        (_, vm) = t `specializes` at
                        rt' = applyTypeMap vm rt
                    in
                    fmap (\srt' ->
                            let
                                lh_mn = map (getLHMeasureName ghci) mn
                            in
                            SpecArg { lh_rep = foldr EApp (EVar symb) $ map EVar lh_mn
                                    , smt_var = "tbd"
                                    , smt_sort = srt'}) $ typeToSort rt') app_meas'

mkSynSpecPB :: String -> [SpecArg] -> PolyBound [SpecArg] -> PolyBound SynthSpec
mkSynSpecPB smt_f arg_ns pb_sa =
    mapPB (\(ui, sa) ->
            let
                ret_ns = map (\(r, i) -> r { smt_var = "x_r_" ++ show ui ++ "_" ++ show i }) $ zip sa ([1..] :: [Integer])
            in
            SynthSpec { sy_name = smt_f ++ show ui
                      , sy_args = arg_ns
                      , sy_rets = ret_ns
                      , sy_coeffs = [] }
        )
        $ zipPB (uniqueIds pb_sa) pb_sa

filterPBByType :: (v -> Type) -> PolyBound v -> Maybe (PolyBound v)
filterPBByType f = filterPB (\(PolyBound v _) ->
                                let
                                    t = f v
                                in
                                not (isTyVar t) && not (isTyFun t))

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

elimSyArgs :: M.Map a SpecInfo -> M.Map a SpecInfo
elimSyArgs = M.map elimSyArgs'

elimSyArgs' :: SpecInfo -> SpecInfo
elimSyArgs' si = si { s_syn_pre = map (mapPB elimSyArgs'') (s_syn_pre si)
                    , s_syn_post = mapPB elimSyArgs'' (s_syn_post si)}

elimSyArgs'' :: SynthSpec -> SynthSpec
elimSyArgs'' sy | take 4 (sy_name sy) == "loop" = sy { sy_args = [] }
elimSyArgs'' sy | take 5 (sy_name sy) == "while" = sy { sy_args = [] }
elimSyArgs'' sy | take 5 (sy_name sy) == "breakWhile" = sy { sy_args = [] }
elimSyArgs'' sy = sy

conflateLoopNames ::  M.Map a SpecInfo -> M.Map a SpecInfo
conflateLoopNames = M.map conflateLoopNames'

conflateLoopNames' :: SpecInfo -> SpecInfo
conflateLoopNames' si@(SI { s_syn_pre = pb_sy_pre@(_:_)
                          , s_syn_post = pb_post@(PolyBound sy_post ps) })
    | take 4 (sy_name sy_post) == "loop" =
        let
            pb_pre = last pb_sy_pre
        in
        si { s_syn_pre = init pb_sy_pre ++ [conflateLoopNames'' pb_pre pb_post] }
conflateLoopNames' si = si

conflateLoopNames'' :: PolyBound SynthSpec -> PolyBound SynthSpec -> PolyBound SynthSpec
conflateLoopNames'' pb1 = mapPB (\(sy1, sy2) -> sy1 { sy_name = sy_name sy2} ) . zipPB pb1

----------------------------------------------------------------------------

typeToSort :: Type -> Maybe Sort
typeToSort (TyApp (TyCon (Name n _ _ _) _) t)
    | n == "Set"
    , Just s <- typeToSort t = Just (SortArray s SortBool)
typeToSort (TyCon (Name n _ _ _) _) 
    | n == "Int"  = Just SortInt
    | n == "Bool" = Just SortBool
    -- | n == "Double"  = Just SortDouble
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

