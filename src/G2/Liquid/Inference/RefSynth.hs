{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.RefSynth ( refSynth
                                    
                                    , grammar
                                    , intRuleList
                                    , boolRuleList

                                    , intSort
                                    , boolSort

                                    , termToLHExpr

                                    , runCVC4
                                    , runCVC4Stream ) where

import G2.Language.Expr
import qualified G2.Language.ExprEnv as E
import G2.Language.Naming
import G2.Language.Syntax as G2
import G2.Language.TypeClasses
import G2.Language.Typing
import G2.Liquid.Conversion
import G2.Liquid.Helpers
import G2.Liquid.Types
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.FuncConstraint
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.PolyRef

import Sygus.LexSygus
import Sygus.ParseSygus
import Sygus.Print
import Sygus.Syntax as Sy
import Language.Haskell.Liquid.Types as LH
import Language.Haskell.Liquid.Types.RefType
import Language.Fixpoint.Types.Constraints
import Language.Fixpoint.Types.Refinements as LH
import qualified Language.Fixpoint.Types as LH

import Control.Exception
import Data.Coerce
import Data.List
import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.Map as M
import Data.Maybe
import Data.Ratio
import qualified Data.Text as T
import Data.Tuple
import Data.Tuple.Extra
import System.Directory
import System.IO
import System.IO.Temp
import qualified System.Process as P

import TyCon

import Debug.Trace

refSynth :: InferenceConfig -> SpecType -> G2.Expr -> TypeClasses -> Measures
         -> MeasureExs -> [FuncConstraint] -> MeasureSymbols -> LH.TCEmb TyCon -> IO (Maybe (PolyBound LH.Expr, [Qualifier]))
refSynth infconfig spc e tc meas meas_ex fc meas_sym tycons = do
        putStrLn "refSynth"
        let (call, f_num, rp_ns) = sygusCall e tc meas meas_ex fc
        let sygus = printSygus call
        putStrLn . T.unpack $ sygus

        -- res <- runCVC4 (T.unpack sygus)
        res <- runCVC4StreamSolutions infconfig f_num (T.unpack sygus)

        case res of
            Left _ -> do
                putStrLn "Timeout"
                return Nothing
                -- error "refSynth: Bad call to CVC4"
            Right smt_st -> do
                let lh_st = refToLHExpr spc rp_ns smt_st meas_sym
                    lh_quals = refToQualifiers spc rp_ns smt_st meas_sym tycons

                print lh_quals

                return $ Just (lh_st, lh_quals)

-------------------------------
-- Constructing Sygus Formula
-------------------------------

sygusCall :: G2.Expr -> TypeClasses -> Measures -> MeasureExs -> [FuncConstraint] -> ([Cmd], Int, RefNamePolyBound)
sygusCall e tc meas meas_ex fcs@(_:_) =
    let
        -- Figure out what measures we need to/can consider
        (arg_ty_c, ret_ty_c, ex_ty_c) = generateRelTypes tc e
        func_ty_c = arg_ty_c ++ [ret_ty_c]
        all_ty_c = func_ty_c ++ ex_ty_c

        rel_arg_ty_c = filter relTy arg_ty_c
        rel_fcs = map (relArgs tc arg_ty_c) fcs

        sorts = typesToSort meas meas_ex all_ty_c

        declare_dts = sortsToDeclareDTs sorts

        (grams, cons, rp_ns) = generateGrammarsAndConstraints sorts meas_ex rel_arg_ty_c ret_ty_c rel_fcs

        call = [ SmtCmd (SetLogic "ALL")]
               ++
               declare_dts
               ++
               [safeModDecl]
               ++
               grams
               ++
               cons
               ++
               [ CheckSynth ]
    in
    (call, length grams, rp_ns)
sygusCall _ _ _ _ _ = error "sygusCall: empty list"

applicableMeasures :: Measures -> Type -> [Name]
applicableMeasures meas t =
    E.keys $ E.filter (applicableMeasure t) meas 

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

generateGrammarsAndConstraints :: TypesToSorts -> MeasureExs -> [Type] -> Type -> [FuncConstraint] -> ([Cmd], [Cmd], RefNamePolyBound)
generateGrammarsAndConstraints sorts meas_ex arg_tys ret_ty fcs@(fc:_) =
    let
        ret_ref_names = refinementNames "ret" (returns $ constraint fc)
        ret_gram_cmds = generateGrammars sorts ret_ref_names meas_ex arg_tys ret_ty

        arg_names_grams = generateParamRefGrammars fc sorts meas_ex arg_tys
        (arg_names, arg_grams_cmds) = unzip arg_names_grams

        cons = generateConstraints sorts meas_ex ret_ref_names arg_tys ret_ty fcs
    in
    (ret_gram_cmds, cons, ret_ref_names)

refinementNames :: String -> G2.Expr -> RefNamePolyBound
refinementNames prefix e =
    let
        poly_bd = extractExprPolyBoundWithRoot e
    in
    mapPB (\i -> prefix ++ "_refinement_" ++ show i) $ uniqueIds poly_bd

generateParamRefGrammars :: FuncConstraint -> TypesToSorts -> MeasureExs -> [Type] -> [(RefNamePolyBound, [Cmd])]
generateParamRefGrammars fc sorts meas_ex arg_tys =
    map (\(i, as@((_, a):_)) ->
            let
                as_tys = map fst as

                arg_ref_names = refinementNames ("args_" ++ show i) a
                arg_gram_cmds = generateGrammars sorts arg_ref_names meas_ex (init as_tys) (last as_tys)
            in
            (arg_ref_names, arg_gram_cmds))
        (zip [0..] . map (zip arg_tys) . filter (not . null) . inits . arguments $ constraint fc)

generateGrammars :: TypesToSorts -> RefNamePolyBound -> MeasureExs -> [Type] -> Type -> [Cmd]
generateGrammars sorts ref_names meas_ex arg_tys ret_ty =
    let
        rt_bound = extractTypePolyBound ret_ty
        ns_rt = zipPB ref_names rt_bound
    in
    map (uncurry (generateSynthFun sorts arg_tys))
        . filter (relTy . snd) 
        $ extractValues ns_rt

generateSynthFun :: TypesToSorts 
                 -> [Type] -- ^ Argument types
                 -> String -- ^ Name of function to synthesize
                 -> Type -- ^ Return type
                 -> Cmd
generateSynthFun sorts arg_tys n rt =
    let
        param_vars = generateParams sorts arg_tys

        ret_sort_var = SortedVar "r" (typeToSort sorts rt)
        sort_vars = param_vars ++ [ret_sort_var]
        
        gram = grammar param_vars ret_sort_var sorts
    in
    SynthFun n sort_vars boolSort (Just gram)

generateParams :: TypesToSorts -> [Type] -> [SortedVar]
generateParams sorts arg_tys =
    let
        varN = map (\i -> "x" ++ show i) ([0..] :: [Integer])
    in
    map (uncurry SortedVar) . zip varN
        . map (typeToSort sorts) . filter (not . isLHDict) $ arg_tys
    where
        isLHDict e
            | (TyCon (Name n _ _ _) _):_ <- unTyApp e = n == "lh"
            | otherwise = False

-------------------------------
-- define-fun
-------------------------------

-- We define a function safe-mod, which forces the denominator of mod to be positive.

safeModSymb :: Symbol
safeModSymb = "safe-mod"

safeModDecl :: Cmd
safeModDecl =
    SmtCmd
        . DefineFun safeModSymb [SortedVar "x" intSort, SortedVar "y" intSort] intSort
            $ TermCall (ISymb "mod")
                [ TermIdent (ISymb "x")
                , TermCall (ISymb "+") [TermLit (LitNum 1), TermCall (ISymb "abs") [TermIdent (ISymb "y")]]
                ]

-------------------------------
-- Grammar
-------------------------------

grammar :: [SortedVar] -> SortedVar -> TypesToSorts -> GrammarDef
grammar arg_sort_vars ret_sorted_var sorts =
    let
        sorted_vars = arg_sort_vars ++ [ret_sorted_var]

        sorts' = filterToSorts (map (\(SortedVar _ s) -> sortSymb s) sorted_vars) sorts

        gramNames = zip (map (\i -> "G" ++ show i) ([0..] :: [Integer])) (allSortNames sorts')
        grams = map (\(g, s_symb) -> (g, IdentSort . ISymb $ s_symb)) gramNames
        sortsToGN = HM.fromList $ map swap gramNames

        brl = GroupedRuleList "B" boolSort
                (boolRuleList ++ addSelectors sortsToGN boolSort sorts')

        irl = GroupedRuleList "I" intSort
                (intRuleList ++ addSelectors sortsToGN intSort sorts')

        drl = GroupedRuleList "D" doubleSort
                (doubleRuleList ++ addSelectors sortsToGN doubleSort sorts')

        const_int = GroupedRuleList "IConst" intSort [GConstant intSort]

        const_double = GroupedRuleList "DConst" doubleSort [GConstant doubleSort]
    
        grm = GrammarDef
                ([ SortedVar "B" boolSort
                 , SortedVar "I" intSort
                 , SortedVar "IConst" intSort
                 , SortedVar "D" doubleSort
                 , SortedVar "DConst" doubleSort ]
                 ++ map (uncurry SortedVar) grams)
                ([ brl
                 , irl
                 , const_int
                 , drl
                 , const_double
                 ]
                 ++ map (uncurry dtGroupRuleList) grams)
    in
    forceVarInGrammar ret_sorted_var grm
    where
        sortSymb (IdentSort (ISymb s)) = s
        sortSymb _ = error "grammar: sortSymb"

intRuleList :: [GTerm]
intRuleList =
    [ GVariable intSort
    -- , GConstant intSort
    , GBfTerm $ BfIdentifierBfs (ISymb "+") [intBf, intBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "+") [intBf, BfIdentifier (ISymb "IConst")]
    , GBfTerm $ BfIdentifierBfs (ISymb "-") [intBf, intBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "*") [intBf, intBf]
    , GBfTerm $ BfIdentifierBfs (ISymb safeModSymb) [intBf, BfIdentifier (ISymb "IConst")]
    ]
    ++ [GBfTerm . BfLiteral . LitNum $ x | x <- [0..0]]

doubleRuleList :: [GTerm]
doubleRuleList =
    [ GVariable doubleSort
    -- , GConstant intSort
    , GBfTerm $ BfIdentifierBfs (ISymb "+") [doubleBf, doubleBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "+") [doubleBf, BfIdentifier (ISymb "DConst")]
    , GBfTerm $ BfIdentifierBfs (ISymb "-") [doubleBf, doubleBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "*") [doubleBf, doubleBf]
    ]
    ++ [GBfTerm . BfLiteral . LitNum $ x | x <- [0..0]]

boolRuleList :: [GTerm]
boolRuleList =
    [ GVariable boolSort
    , GConstant boolSort
    
    , GBfTerm $ BfIdentifierBfs (ISymb "=") [intBf, intBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "<") [intBf, intBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "<=") [intBf, intBf]

    , GBfTerm $ BfIdentifierBfs (ISymb "=") [doubleBf, doubleBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "<") [doubleBf, doubleBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "<=") [doubleBf, doubleBf]

    , GBfTerm $ BfIdentifierBfs (ISymb "=>") [boolBf, boolBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "and") [boolBf, boolBf]
    -- , GBfTerm $ BfIdentifierBfs (ISymb "or") [boolBf, boolBf]
    -- , GBfTerm $ BfIdentifierBfs (ISymb "not") [boolBf]
    ]

elimHigherOrderArgs :: FuncConstraint -> FuncConstraint
elimHigherOrderArgs fc =
    let
        cons = constraint fc
        as = arguments cons
        as' = filter (not . isTyFun . typeOf) as
    in
    fc { constraint = cons { arguments = as' }}

dtGroupRuleList :: Symbol -> Sort -> GroupedRuleList
dtGroupRuleList symb srt = GroupedRuleList symb srt [GVariable srt]

intBf :: BfTerm
intBf = BfIdentifier (ISymb "I")

doubleBf :: BfTerm
doubleBf = BfIdentifier (ISymb "D")

boolBf :: BfTerm
boolBf = BfIdentifier (ISymb "B")

intSort :: Sort
intSort = IdentSort (ISymb "Int")

doubleSort :: Sort
doubleSort = IdentSort (ISymb "Real")

boolSort :: Sort
boolSort = IdentSort (ISymb "Bool")

relArgs :: TypeClasses -> [Type] -> FuncConstraint -> FuncConstraint
relArgs tc ts fc =
    let
        cons = constraint fc
        as = filter (relArg tc) $ arguments cons
        ts_as = zip ts as
        as' = map snd $ filter (relTy . fst) ts_as
    in
    fc { constraint = cons { arguments = as' }}

relArg :: TypeClasses -> G2.Expr -> Bool
relArg tc e = (not . isTypeClass tc . typeOf $ e) && (not . isType $ e)
    where
        isType (Type _) = True
        isType _ = False

type ArgTys = [Type]
type RetType = Type
type PolyTypes = [Type]

generateRelTypes :: TypeClasses -> G2.Expr -> (ArgTys, RetType, PolyTypes)
generateRelTypes tc e =
    let
        ty_e = PresType $ inTyForAlls (typeOf e)
        arg_ty_c = filter (not . isTYPE)
                 . filter (not . isTypeClass tc)
                 $ argumentTypes ty_e
        ret_ty_c = returnType ty_e

        ex_ty_c = tail $ unTyApp ret_ty_c
    in
    (arg_ty_c, ret_ty_c, ex_ty_c)

-- | Is the given type usable by SyGuS?
relTy :: Type -> Bool
relTy (TyVar _) = False
relTy (TyFun _ _) = False
relTy _ = True


-------------------------------
-- Constraints
-------------------------------

-- | Constraints expresessed as "anded" terms
data TermConstraint = PosT { term_cons :: [Term] }
                    | NegT { term_cons :: [Term] }
                    deriving (Show, Read)

modifyTC :: ([Term] -> [Term]) -> TermConstraint -> TermConstraint
modifyTC f tc = tc { term_cons = f (term_cons tc) }

-- | Convert constraints.  Measures cause us to lose information about the data, so after
-- conversion we can have a constraint both postively and negatively.  We know that the postive
-- constraint corresponds to an actual execution, so we keep that one, adnd drop the negative constraint.

generateConstraints :: TypesToSorts -> MeasureExs -> RefNamePolyBound -> [Type] -> Type -> [FuncConstraint] -> [Cmd]
generateConstraints sorts meas_ex poly_names arg_tys ret_ty fcs = 
    let
        cons = map (termConstraints sorts meas_ex poly_names arg_tys ret_ty) fcs
        cons' = filterPosAndNegConstraints cons
        cons'' = map termConstraintToConstraint cons'

        exists = existentialConstraints sorts meas_ex poly_names arg_tys ret_ty
    in
    exists ++ cons''

-- | Prevents any refinements from being set to "False" (or equivalent, i.e. 0 < 0)
existentialConstraints :: TypesToSorts -> MeasureExs -> RefNamePolyBound -> [Type] -> Type -> [Cmd]
existentialConstraints sorts meas_ex poly_names arg_tys ret_ty =
    let
        rt_bound = extractTypePolyBound ret_ty
        ns_rt = zipPB rt_bound poly_names
    in
    mapMaybe (fmap Constraint . uncurry (existentialTerms sorts meas_ex arg_tys)) $ extractValues ns_rt


existentialTerms :: TypesToSorts -> MeasureExs -> [Type] -> Type -> String -> Maybe Term
existentialTerms _ _ _ (TyVar _) _ = Nothing
existentialTerms sorts meas_ex arg_tys ret_ty fn =
    let
        ar_vs = map (\(i, t) -> ("arg" ++ show i, typeToSort sorts t)) $ zip [0..] arg_tys
        srt_v = ("e_ret", typeToSort sorts ret_ty)
    in
    Just . TermExists (map (uncurry SortedVar) $ srt_v:ar_vs)
        $ TermCall (ISymb fn) (map (TermIdent . ISymb . fst) ar_vs ++ [TermIdent (ISymb "e_ret")])

termConstraints :: TypesToSorts -> MeasureExs -> RefNamePolyBound -> [Type] -> Type -> FuncConstraint -> TermConstraint
termConstraints sorts meas_ex poly_names arg_tys ret_ty (Pos fc) =
    PosT $ funcCallTerm sorts meas_ex poly_names arg_tys ret_ty fc
termConstraints sorts meas_ex poly_names arg_tys ret_ty (Neg fc) =
    NegT $ funcCallTerm sorts meas_ex poly_names arg_tys ret_ty fc

-- When polymorphic arguments are instantiated with values, we use those as
-- arguments for the polymorphic refinement functions.  However, even when they
-- do not have values, we still want to enforce that (for some value) the polymorphic
-- refinement function is true.  Thus, given arguments a_1, ..., a_n, we need to add
-- an expression of the form:
--      exists x . r(a_1, ..., a_n, x)

data ValOrExistential v = Val v | Existential

funcCallTerm :: TypesToSorts -> MeasureExs -> RefNamePolyBound ->  [Type] -> Type -> FuncCall -> [Term]
funcCallTerm sorts meas_ex poly_names arg_tys ret_ty (FuncCall { arguments = ars, returns = r}) =
    let
        r_bound = extractExprPolyBoundWithRoot r
        rt_bound = extractTypePolyBound ret_ty
        ns_r_bound = zip3PB r_bound rt_bound poly_names
        ns_r_bound' = concatMap expand1 (extractValues ns_r_bound)
    in
    mapMaybe (\(r, rt, n) -> funcCallTerm' sorts meas_ex arg_tys ars r rt n) $ ns_r_bound' -- r
    where
        expand1 :: ([a], b, c) -> [(ValOrExistential a, b, c)]
        expand1 ([], b, c) = [(Existential, b, c)]
        expand1 (as, b, c) = map (\a -> (Val a, b, c)) as 

funcCallTerm' :: TypesToSorts -> MeasureExs -> [Type] -> [G2.Expr] -> ValOrExistential G2.Expr -> Type -> String -> Maybe Term
funcCallTerm' sorts meas_ex arg_tys ars r ret_ty fn
    | Val r' <- r
    , relTy ret_ty =
        let
            trm_ret = exprToTerm sorts meas_ex ret_ty r'
        in
        Just $ TermCall (ISymb fn) (trm_ars ++ [trm_ret])
    | Existential <- r
    , relTy ret_ty =
        let
            srt_v = SortedVar "e_ret" $ typeToSort sorts ret_ty
        in
        Just . TermExists [srt_v] $ TermCall (ISymb fn) (trm_ars ++ [TermIdent (ISymb "e_ret")])
    | otherwise = Nothing
    where
        trm_ars = map (uncurry (exprToTerm sorts meas_ex)) (zip arg_tys ars)


exprToTerm :: TypesToSorts -> MeasureExs -> Type -> G2.Expr -> Term
exprToTerm _ _ (TyCon (Name "Bool" _ _ _) _) (Data (DataCon (Name n _ _ _) _))
    | "True" <- n = TermLit $ LitBool True
    | "False" <- n =TermLit $ LitBool False
exprToTerm _ _ (TyCon (Name n _ _ _) _) (App _ (Lit l))
    |  n == "Int"
    || n == "Float"
    || n == "Double" = litToTerm l
exprToTerm _ _ _ (Lit l) = litToTerm l
exprToTerm sorts meas_ex t e = exprToDTTerm sorts meas_ex t e
exprToTerm _ _ _ e = error $ "exprToTerm: Unhandled Expr " ++ show e

litToTerm :: G2.Lit -> Term
litToTerm (LitInt i) = TermLit (LitNum i)
litToTerm (LitDouble d) = TermCall (ISymb "/") [ TermLit . LitNum $ numerator d
                                               , TermLit . LitNum $ denominator d]
litToTerm _ = error "litToTerm: Unhandled Lit"

exprToDTTerm :: TypesToSorts -> MeasureExs -> Type -> G2.Expr -> Term
exprToDTTerm sorts meas_ex t e =
    case lookupSort t sorts of
        Just si
            | not . null $ meas_names si ->
                TermCall (ISymb (dt_name si)) $ map (measVal sorts meas_ex e) (meas_names si)
            | otherwise -> TermIdent (ISymb (dt_name si))
        Nothing -> error $ "exprToDTTerm: No sort found" ++ "\nsorts = " ++ show sorts ++ "\nt = " ++ show t ++ "\ne = " ++ show e

filterPosAndNegConstraints :: [TermConstraint] -> [TermConstraint]
filterPosAndNegConstraints ts =
    let
        tre = concatMap term_cons $ filter isPosT ts
    in
    filter (not . null . term_cons)
        $ map (\t -> if isPosT t then t else modifyTC (filter (not . flip elem tre)) t) ts
    -- filter (\t -> isPosT t || all (\t' -> term_cons t /= term_cons t') tre ) ts
    where
        isPosT (PosT _) = True
        isPosT (NegT _) = False

termConstraintToConstraint :: TermConstraint -> Cmd
termConstraintToConstraint (PosT ts) = Constraint $ TermCall (ISymb "and") ts
termConstraintToConstraint (NegT ts) = Constraint $ TermCall (ISymb "not") [TermCall (ISymb "and") ts]

typeToSort :: TypesToSorts -> Type -> Sort
typeToSort _ (TyCon (Name n _ _ _) _) 
    | n == "Int" = intSort
    | n == "Double" = doubleSort
    | n == "Bool" = boolSort
typeToSort sm t
    | Just si <- lookupSort t sm = IdentSort (ISymb $ sort_name si)
typeToSort sm t = error $ "Unknown Type\n" ++ show t ++ "\nsm = " ++ show sm

-------------------------------
-- Measures
-------------------------------

measVal :: TypesToSorts -> MeasureExs -> G2.Expr -> SortedVar -> Term
measVal sorts meas_ex e (SortedVar mn _) =
    let
        meas_n = strToName mn
    in
    case HM.lookup e meas_ex of
        Just meas_out
            | Just (_, v) <- find (\(n', _) -> nameOcc meas_n == nameOcc n') meas_out -> exprToTerm sorts meas_ex (typeOf v) v
        Nothing -> error $ "measVal: Expr not found\nmeas_ex = " ++ show meas_ex ++ "\ne = " ++ show e

newtype TypesToSorts = TypesToSorts { types_to_sorts :: [(Type, SortInfo)] }
                       deriving (Show, Read)

data SortInfo = SortInfo { sort_name :: Symbol
                         , dt_name :: Symbol
                         , meas_names :: [SortedVar]}
                         deriving (Show, Read)

typesToSort :: Measures -> MeasureExs -> [Type] -> TypesToSorts
typesToSort meas meas_ex ty_c =
    let
        rel_ty_c = filter relTy ty_c

        rel_ty_c' = nubBy (\t1 t2 -> t1 .::. t2) rel_ty_c
        dt_ts = filter (not . isPrimTy) rel_ty_c' 

        ns = concatMap (map fst) . HM.elems $ meas_ex
        applic_meas = map (applicableMeasures meas) dt_ts
        applic_meas' = map (filter (\m -> m `elem` ns)) applic_meas
        meas_ids = map (map (\n -> Id n (returnType (case E.lookup n meas of
                                                        Just e -> e
                                                        Nothing -> error "sygusCall: No type found")))) applic_meas'

        meas_ids' = filterNonPrimMeasure meas_ids

        ts_applic_meas = zip dt_ts meas_ids'
    in
    typesToSort' ts_applic_meas
    
isPrimTy :: Type -> Bool    
isPrimTy (TyCon (Name "Int" _ _ _) _) = True
isPrimTy (TyCon (Name "Double" _ _ _) _) = True
isPrimTy (TyCon (Name "Bool" _ _ _) _) = True
isPrimTy _ = False

typesToSort' :: [(Type, [Id])] -> TypesToSorts
typesToSort' ts =
    let
        ts_s = map (\(i, (t, ns)) -> typesToSort'' i t ns) $ zip [0..] ts
    in
    TypesToSorts ts_s

typesToSort'' :: Int -> Type -> [Id] -> (Type, SortInfo)
typesToSort'' i t ns =
    let
        srt = "Sort_" ++ show i
        dt = "DT_" ++ show i
        sel_svs = map (\is@(Id (Name n m _ _) _) -> SortedVar
                                (nameToStr (Name n m i Nothing)) (typeToSort (TypesToSorts [])
                                (typeOf is))
                      ) ns
    in
    (t, SortInfo { sort_name = srt, dt_name = dt, meas_names = sel_svs })

lookupSort :: Type -> TypesToSorts -> Maybe SortInfo
lookupSort t (TypesToSorts sorts) =
    let
        sis = filter (\(t', _) -> PresType t .:: t') sorts
        min_sis = filter (\(t', _) -> all (\(t'', _) -> PresType t' .:: t'') sis) sis
    in
    case min_sis of
        [(_, si)] -> Just si
        [] -> Nothing
        _ -> error $ "t = " ++ show t ++ "\nmin_sis = " ++ show min_sis

     -- = fmap (snd) . find (\(t', _) -> PresType t .:: t') . types_to_sorts

sortsToDeclareDTs :: TypesToSorts -> [Cmd]
sortsToDeclareDTs = map (sortToDeclareDT) . map snd . types_to_sorts

sortToDeclareDT :: SortInfo -> Cmd
sortToDeclareDT (SortInfo {sort_name = srt, dt_name = dtn, meas_names = sels}) =
    SmtCmd . DeclareDatatype srt $ DTDec [DTConsDec dtn sels]

filterNonPrimMeasure :: [[Id]] -> [[Id]]
filterNonPrimMeasure = map (filter isPrimMeasure)

isPrimMeasure :: Id -> Bool
isPrimMeasure = isPrimTy . typeOf

allSorts :: TypesToSorts -> [Sort]
allSorts = map (IdentSort . ISymb) . allSortNames

allSortNames :: TypesToSorts -> [Symbol]
allSortNames = map (sort_name . snd) . types_to_sorts

addSelectors :: HM.HashMap Symbol String -> Sort -> TypesToSorts -> [GTerm]
addSelectors grams s =
    concatMap (\si ->
            case HM.lookup (sort_name si) grams of 
                Just gn -> mapMaybe (addSelector gn s) (meas_names si)
                Nothing -> error "addSelectors: Grammar name not found") . map snd . types_to_sorts

addSelector :: Symbol -> Sort -> SortedVar -> Maybe GTerm
addSelector gn s (SortedVar ident vs)
    | s == vs = Just . GBfTerm $ BfIdentifierBfs (ISymb ident) [BfIdentifier (ISymb gn)]
    | otherwise = Nothing

filterToSorts :: [Symbol] -> TypesToSorts -> TypesToSorts
filterToSorts xs (TypesToSorts sorts) =
    TypesToSorts $ filter (\(_, s) -> any (sort_name s ==) xs) sorts

-------------------------------
-- Enforcing return value use
-------------------------------

-- Adjusts a grammar to force using a given GTerm

forceVarInGrammar :: SortedVar -> GrammarDef -> GrammarDef
forceVarInGrammar var (GrammarDef sv grls) =
    let
        prod_srt = mapMaybe (\grl@(GroupedRuleList grl_symb srt' _) ->
                            if canProduceVar var grl
                                then Just grl_symb
                                else Nothing ) grls

        reach = gramSymbReachableFrom prod_srt grls

        sv_reach = concatMap (grammarDefSortedVars reach) sv
    in
    GrammarDef sv_reach $ forceVarInGRLList var reach grls

forceVarInGRLList :: SortedVar -> [Symbol] -> [GroupedRuleList] -> [GroupedRuleList]
forceVarInGRLList var reach grls =
    let
        fv_map = HM.fromList $ map (\n -> (toBf n, toBf $ forcedVarSymb n)) reach

    in
    concatMap (forceVarInGRL var reach fv_map) grls
    where
        toBf = BfIdentifier . ISymb

forceVarInGRL :: SortedVar -> [Symbol] -> HM.HashMap BfTerm BfTerm -> GroupedRuleList -> [GroupedRuleList]
forceVarInGRL (SortedVar sv_symb sv_srt) reach fv_map grl@(GroupedRuleList grl_symb grl_srt gtrms)
    | grl_symb `elem` reach
    , sv_srt == grl_srt =
        let
            bf_var = BfIdentifier (ISymb sv_symb)
            fv_gtrms' = GBfTerm bf_var:elimVariable fv_gtrms
        in
        [GroupedRuleList fv_symb grl_srt fv_gtrms', grl]
    | grl_symb `elem` reach = [GroupedRuleList fv_symb grl_srt fv_gtrms, grl]
    | otherwise = [grl]
    where
        fv_symb = forcedVarSymb grl_symb
        fv_gtrms = substOnceGTerms fv_map gtrms


forcedVarSymb :: Symbol -> Symbol
forcedVarSymb = ("fv_" ++)

elimVariable :: [GTerm] -> [GTerm]
elimVariable = filter (\t -> case t of
                            GVariable _ -> False
                            _ -> True)

grammarDefSortedVars :: [Symbol] -> SortedVar -> [SortedVar]
grammarDefSortedVars symbs sv@(SortedVar n srt)
    | n `elem` symbs = [SortedVar (forcedVarSymb n) srt, sv]
    | otherwise = [sv]

-- Can a GroupedRuleList produce a given variable?

canProduceVar :: SortedVar -> GroupedRuleList -> Bool
canProduceVar var@(SortedVar symb sv_srt) (GroupedRuleList _ grl_srt gtrms)
    | sv_srt == grl_srt = any (canProduceVarGTerm var) gtrms
    | otherwise = False

canProduceVarGTerm :: SortedVar -> GTerm -> Bool
canProduceVarGTerm (SortedVar _ sv_srt) (GVariable gv_srt) = sv_srt == gv_srt
canProduceVarGTerm (SortedVar s _) (GBfTerm (BfIdentifier (ISymb is))) = s == is
canProduceVarGTerm _ (GConstant _) = False

-- Reachability checks

gramSymbReachableFrom :: [Symbol] -> [GroupedRuleList] -> [Symbol]
gramSymbReachableFrom = gramSymbReachableFrom' HS.empty

gramSymbReachableFrom' :: HS.HashSet Symbol -> [Symbol] -> [GroupedRuleList] -> [Symbol]
gramSymbReachableFrom' searched [] _ = HS.toList searched
gramSymbReachableFrom' searched (x:xs) grls
    | x `HS.member` searched = gramSymbReachableFrom' searched xs grls
    | otherwise =
        let
            contains_x = map (\(GroupedRuleList s _ _) -> s)
                       $ filter (containsSymbol x) grls
        in
        gramSymbReachableFrom' (HS.insert x searched) (contains_x ++ xs) grls

containsSymbol :: Symbol -> GroupedRuleList -> Bool
containsSymbol symb (GroupedRuleList _ _ gtrms) = any (containsSymbolGTerm symb) gtrms

containsSymbolGTerm :: Symbol -> GTerm -> Bool
containsSymbolGTerm symb (GBfTerm bf) = containsSymbolBfTerm symb bf
containsSymbolGTerm _ _ = False

containsSymbolBfTerm :: Symbol -> BfTerm -> Bool
containsSymbolBfTerm symb (BfIdentifier ident) = containsSymbolIdent symb ident
containsSymbolBfTerm symb (BfIdentifierBfs ident bfs) =
    containsSymbolIdent symb ident || any (containsSymbolBfTerm symb) bfs
containsSymbolBfTerm _ (BfLiteral _) = False

containsSymbolIdent :: Symbol -> Identifier -> Bool
containsSymbolIdent symb (ISymb symb') = symb == symb'
containsSymbolIdent symb _ = False

-- Substitution functions

substOnceGRL :: HM.HashMap BfTerm BfTerm -> GroupedRuleList -> GroupedRuleList
substOnceGRL m (GroupedRuleList symb srt gtrms) =
    GroupedRuleList symb srt $ substOnceGTerms m gtrms

substOnceGTerms :: HM.HashMap BfTerm BfTerm -> [GTerm] -> [GTerm]
substOnceGTerms m = concatMap (substOnceGTerm m)

substOnceGTerm :: HM.HashMap BfTerm BfTerm -> GTerm -> [GTerm]
substOnceGTerm m (GBfTerm bf) = map GBfTerm $ substOnceBfTerm m bf
substOnceGTerm _ gt = [gt]

substOnceBfTerm :: HM.HashMap BfTerm BfTerm -> BfTerm -> [BfTerm]
substOnceBfTerm m (BfIdentifierBfs c bfs) = map (BfIdentifierBfs c) $ substsOnces m bfs
substOnceBfTerm _ bf = [bf]

substOnceTerm :: HM.HashMap Term Term -> Term -> [Term]
substOnceTerm m (TermCall c ts) = map (TermCall c) $ substsOnces m ts
substOnceTerm _ t = [t]

-- | Given:
--      * A mapping of list element to be replaced, to new elements
--      * A list, xs
-- returns a list of new lists.  Each new list is xs, but with exactly one
-- occurence of an old element replaced by the corresponding new element.
substsOnces :: (Eq a, Hashable a) => HM.HashMap a a -> [a] -> [[a]]
substsOnces m = substsOnces' m []

substsOnces' :: (Eq a, Hashable a) => HM.HashMap a a -> [a] -> [a] -> [[a]]
substsOnces' m rv [] = []
substsOnces' m rv (x:xs)
    | Just new <- HM.lookup x m = (reverse rv ++ new:xs):rst
    | otherwise = rst
        where
            rst = substsOnces' m (x:rv) xs

-------------------------------
-- Converting to refinement
-------------------------------

stripUnsat :: String -> String
stripUnsat ('u':'n':'s':'a':'t':xs) = xs
stripUnsat xs = xs

refToQualifiers :: SpecType -> RefNamePolyBound -> [Cmd] -> MeasureSymbols -> LH.TCEmb TyCon -> [Qualifier]
refToQualifiers st rp_ns cmds meas_sym tycons =
    let
        termsPB = defineFunsPB cmds rp_ns
        (lh_e, ars, ret) = refToLHExpr' st termsPB meas_sym
    in
    map (uncurry (refToQualifier tycons ars)) . extractValues $ zipPB ret lh_e

refToQualifier :: LH.TCEmb TyCon -> [(LH.Symbol, SpecType)] -> (LH.Symbol, SpecType) -> LH.Expr -> Qualifier
refToQualifier tycons ars ret e =
    Q { qName = "G2"
      , qParams = map (mkParam tycons) (ret:ars)
      , qBody = e
      , qPos = LH.dummyPos "G2" }

mkParam :: LH.TCEmb TyCon -> (LH.Symbol, SpecType) -> (LH.Symbol, LH.Sort)
mkParam tycons (symb, st) = (symb, funcHead $ rTypeSort tycons st)
    where
        funcHead (LH.FFunc h _) = h
        funcHead s = s

refToLHExpr :: SpecType -> RefNamePolyBound -> [Cmd] -> MeasureSymbols -> PolyBound LH.Expr
refToLHExpr st rp_ns cmds meas_sym =
    let
        termsPB = defineFunsPB cmds rp_ns
        -- termsPB' = shiftPB termsPB
    
        (lh_e, _, _) = refToLHExpr' st termsPB meas_sym
    in
    lh_e

defineFunsPB :: [Cmd] -> RefNamePolyBound -> PolyBound ([SortedVar], Term)
defineFunsPB cmds = mapPB (defineFunsPB' cmds)

defineFunsPB' :: [Cmd] -> String -> ([SortedVar], Term)
defineFunsPB' cmds fn
    | Just (SmtCmd (DefineFun _ ars _ trm)) <- find (\(SmtCmd (DefineFun n _ _ _)) -> n == fn) cmds =
        (ars, trm)
    | otherwise = ([], TermLit (LitBool True))

-- | Shift all terms up as much as possible.  This avoids expressions being nested more deeply-
-- and thus (in G2) checked more frequently- than needed.
shiftPB :: PolyBound ([SortedVar], Term) -> PolyBound ([SortedVar], Term)
shiftPB pb =
    let
        pb' = shiftPB' pb
    in
    if pb == pb' then pb else shiftPB pb'

shiftPB' :: PolyBound ([SortedVar], Term) -> PolyBound ([SortedVar], Term)
shiftPB' (PolyBound svt@(sv, t) svts) =
    let
        (shift, leave) =
            partition
                (\(PolyBound (sv', t') _) ->
                    let
                        t_syms = termSymbols t'
                    in
                    case sv' of
                        [] -> False
                        _ -> let SortedVar s _ = (last sv') in s `notElem` t_syms) svts

        sv_new = nub $ sv ++ concatMap (\(PolyBound (sv', _) _) -> sv') shift
        t_new =
            case shift of
                [] -> t
                _ -> TermCall (ISymb "and") $ t:map (\(PolyBound (_, t') _) -> t') shift

        shift_new = map (\(PolyBound _ pb) -> PolyBound ([], TermLit (LitBool True)) pb) shift
    in
    PolyBound (sv_new, t_new) (shift_new ++ leave)

refToLHExpr' :: SpecType
             -> PolyBound ([SortedVar], Term) 
             -> MeasureSymbols
             -> (PolyBound LH.Expr, [(LH.Symbol, SpecType)], PolyBound (LH.Symbol, SpecType))
refToLHExpr' st pb_sv_t meas_sym =
    let
        (ars_st, ret_st) = specTypePieces st
        ars_symb_st = map (\(s, i) -> (specTypeSymbol s, s)) $ zip ars_st [0..]
        ret_symb_st = mapPB (\s -> (specTypeSymbol s, s))  ret_st

        ars = map fst ars_symb_st
        ret = mapPB fst ret_symb_st

        pb_sv_t_ret = mapPB (\((sv, t), r) -> (sv, t, r)) $ zipPB pb_sv_t ret
    in
    (mapPB (uncurry3 (refToLHExpr'' meas_sym ars )) pb_sv_t_ret, ars_symb_st, ret_symb_st)

refToLHExpr'' :: MeasureSymbols -> [LH.Symbol] -> [SortedVar] -> Term -> LH.Symbol -> LH.Expr
refToLHExpr'' meas_sym symbs ars trm ret =
    let
        ars' = map (\(SortedVar sym _) -> sym) ars

        -- This is a bit of a dirty hack.  The relArgs function drops typeclasses,
        -- so that we don't have to deal with them in the SyGuS solver.  But we still
        -- gather the bindings for the typeclasses with specTypeSymbols.
        -- Fortunately, the typeclasses are always the first arguments in the list,
        -- so we can simply take the correct number of arguments from the end of the list.
        last_symbs = reverse . take (length ars - 1) $ reverse symbs

        symbsArgs = M.fromList $ zip ars' (last_symbs ++ [ret])
    in
    termToLHExpr meas_sym symbsArgs trm

termToLHExpr :: MeasureSymbols -> M.Map Sy.Symbol LH.Symbol -> Term -> LH.Expr
termToLHExpr _ m_args (TermIdent (ISymb v)) =
    case M.lookup v m_args of
        Just v' -> EVar v'
        Nothing -> error "termToLHExpr: Variable not found"
termToLHExpr _ _ (TermLit l) = litToLHConstant l
termToLHExpr meas_sym@(MeasureSymbols meas_sym') m_args (TermCall (ISymb v) ts)
    -- Measures
    | Just meas <- find (\meas' -> Just (symbolName meas') == fmap zeroName (maybe_StrToName v)) meas_sym' =
        foldl' EApp (EVar meas) $ map (termToLHExpr meas_sym m_args) ts
    -- EBin
    | "+" <- v
    , [t1, t2] <- ts = EBin LH.Plus (termToLHExpr meas_sym m_args t1) (termToLHExpr meas_sym m_args t2)
    | "-" <- v
    , [t1] <- ts = ENeg (termToLHExpr meas_sym m_args t1)
    | "-" <- v
    , [t1, t2] <- ts = EBin LH.Minus (termToLHExpr meas_sym m_args t1) (termToLHExpr meas_sym m_args t2)
    | "*" <- v
    , [t1, t2] <- ts = EBin LH.Times (termToLHExpr meas_sym m_args t1) (termToLHExpr meas_sym m_args t2)
    | "mod" <- v
    , [t1, t2] <- ts = EBin LH.Mod (termToLHExpr meas_sym m_args t1) (termToLHExpr meas_sym m_args t2)
    -- Special handling for safe-mod.  We enforce via the grammar that the denominator is an Integer
    | "safe-mod" <- v
    , [t1, t2] <- ts
    , TermLit (LitNum n) <- t2 = EBin LH.Mod (termToLHExpr meas_sym m_args t1) (ECon (I ((abs n) + 1)))
    -- More EBin...
    | "and" <- v = PAnd $ map (termToLHExpr meas_sym m_args) ts
    | "or" <- v = POr $ map (termToLHExpr meas_sym m_args) ts
    | "not" <- v, [t1] <- ts = PNot (termToLHExpr meas_sym m_args t1)
    | "=>" <- v
    , [t1, t2] <- ts = PImp (termToLHExpr meas_sym m_args t1) (termToLHExpr meas_sym m_args t2)
    -- PAtom
    | "=" <- v
    , [t1, t2] <- ts = PAtom LH.Eq (termToLHExpr meas_sym m_args t1) (termToLHExpr meas_sym m_args t2)
    | ">" <- v 
    , [t1, t2] <- ts = PAtom LH.Gt (termToLHExpr meas_sym m_args t1) (termToLHExpr meas_sym m_args t2)
     | ">=" <- v 
    , [t1, t2] <- ts = PAtom LH.Ge (termToLHExpr meas_sym m_args t1) (termToLHExpr meas_sym m_args t2)
    | "<" <- v 
    , [t1, t2] <- ts = PAtom LH.Lt (termToLHExpr meas_sym m_args t1) (termToLHExpr meas_sym m_args t2)
   | "<=" <- v 
    , [t1, t2] <- ts = PAtom LH.Le (termToLHExpr meas_sym m_args t1) (termToLHExpr meas_sym m_args t2)
    -- More PAtom...
termToLHExpr meas_sym@(MeasureSymbols meas_sym') m_args (TermCall (ISymb v) ts) =
    error $ "v = " ++ show (maybe_StrToName v) ++ "\nmeas_syms' = " ++ show (map symbolName meas_sym')
termToLHExpr (_) _ t = error $ "termToLHExpr meas_sym m_args: unhandled " ++ show t

zeroName :: Name -> Name
zeroName (Name n m _ l) = Name n m 0 l

litToLHConstant :: Sy.Lit -> LH.Expr
litToLHConstant (LitNum n) = ECon (I n)
litToLHConstant (LitBool b) = if b then PTrue else PFalse
litToLHConstant l = error $ "litToLHConstant: Unhandled literal " ++ show l

-------------------

specTypeSymbols :: SpecType -> ([LH.Symbol], PolyBound LH.Symbol)
specTypeSymbols st =
    let
        (sts, pb_st) = specTypePieces st
    in
    (map specTypeSymbol sts, mapPB specTypeSymbol pb_st)

specTypeSymbol :: SpecType -> LH.Symbol
specTypeSymbol (RFun { rt_bind = b }) = b
specTypeSymbol (RApp { rt_reft = ref }) = reftSymbol $ ur_reft ref
specTypeSymbol (RVar { rt_reft = ref }) = reftSymbol $ ur_reft ref
specTypeSymbol _ = error $ "specTypeSymbol: SpecType not handled"

specTypePieces :: SpecType -> ([SpecType], PolyBound SpecType)
specTypePieces st = specTypePieces' [] st

specTypePieces' :: [SpecType] -> SpecType -> ([SpecType], PolyBound SpecType)
specTypePieces' sts rfun@(RFun { rt_in = i, rt_out = out }) =
    case i of
        RVar {} -> specTypePieces' sts out
        RFun {} -> specTypePieces' sts out
        _ -> specTypePieces' (rfun:sts) out
specTypePieces' sts rapp@(RApp {}) = (reverse sts, specTypeRAppPieces rapp)
specTypePieces' _ (RVar {}) = error "specTypePieces': passed RVar"
specTypePieces' sts (RAllT { rt_ty = out }) = specTypePieces' sts out

specTypeRAppPieces :: SpecType -> PolyBound SpecType
specTypeRAppPieces rapp@(RApp { rt_reft = ref, rt_args = ars }) =
    PolyBound rapp $ map specTypeRAppPieces ars
specTypeRAppPieces rvar@(RVar {}) = PolyBound rvar []
specTypeRAppPieces r = error $ "specTypeRAppPieces: Unexpected SpecType" ++ "\n" ++ show r

-------------------

reftSymbol :: Reft -> LH.Symbol
reftSymbol = fst . unpackReft

unpackReft :: Reft -> (LH.Symbol, LH.Expr) 
unpackReft = coerce

-- | Collects all the symbols from a term
termSymbols :: Term -> [Symbol]
termSymbols (TermIdent i) = identifierSymbols i
termSymbols (TermLit _) = []
termSymbols (TermCall i ts) = identifierSymbols i ++ concatMap termSymbols ts
termSymbols (TermExists sv t) = map svSymbol sv ++ termSymbols t
termSymbols (TermForAll sv t) = map svSymbol sv ++ termSymbols t
termSymbols (TermLet vb t) = concatMap vbSymbols vb ++ termSymbols t

identifierSymbols :: Identifier -> [Symbol]
identifierSymbols (ISymb s) = [s]
identifierSymbol (Indexed s inds) = s:mapMaybe indexSymbol inds

indexSymbol :: Index -> Maybe Symbol
indexSymbol (IndSymb s) = Just s
indexSymbol _ = Nothing

svSymbol :: SortedVar -> Symbol
svSymbol (SortedVar s _) = s

vbSymbols :: VarBinding -> [Symbol]
vbSymbols (VarBinding s t) = s:termSymbols t

-------------------------------
-- Calling SyGuS
-------------------------------

runCVC4 :: String -> IO (Either SomeException String)
runCVC4 sygus =
    try (
        withSystemTempFile ("cvc4_input.sy")
        (\fp h -> do
            hPutStr h sygus
            -- We call hFlush to prevent hPutStr from buffering
            hFlush h

            toCommandOSX <- findExecutable "gtimeout" 
            let toCommand = case toCommandOSX of
                    Just c -> c          -- Mac
                    Nothing -> "timeout" -- Linux

            P.readProcess toCommand (["10", "cvc4", fp, "--lang=sygus2"]) "")
        )

runCVC4StreamSolutions :: InferenceConfig -> Int -> String -> IO (Either SomeException [Cmd])
runCVC4StreamSolutions infconfig grouped sygus =
    try (
        withSystemTempFile ("cvc4_input.sy")
            (\fp h -> do
                hPutStr h sygus
                -- We call hFlush to prevent hPutStr from buffering
                hFlush h

                timeout <- timeOutCommand

                -- --no-sygus-fair-max searches for functions that minimize the sum of the sizes of all functions
                (inp, outp, errp, _) <- P.runInteractiveCommand
                                            $ timeout ++ " " ++ show (timeout_sygus infconfig)
                                                ++ " cvc4 " ++ fp ++ " --lang=sygus2 --sygus-stream --no-sygus-fair-max"

                lnes <- checkIfSolution grouped outp

                hClose inp
                hClose outp
                hClose errp

                return lnes
            )
        )

checkIfSolution :: Int -> Handle -> IO [Cmd]
checkIfSolution grouped h = do
    sol <- getSolution grouped h
    let sol' = concatMap (parse . lexSygus) $ sol
    if all (\c -> rInCmd c || noVarInCmd c) sol' then return sol' else checkIfSolution grouped h 

getSolution :: Int -> Handle -> IO [String]
getSolution 0 _ = return []
getSolution !n h = do
    lne <- hGetLine h
    lnes <- getSolution (n - 1) h
    return $ lne:lnes

rInCmd :: Cmd -> Bool
rInCmd (SmtCmd (DefineFun _ _ _ t)) = rInTerm t
rInCmd _ = False

rInTerm :: Term -> Bool
rInTerm (TermIdent (ISymb n)) = n == "r"
rInTerm (TermIdent _) = False
rInTerm (TermLit _) = False
rInTerm (TermCall _ ts) = any rInTerm ts
rInTerm (TermExists _ t) = rInTerm t
rInTerm (TermForAll _ t) = rInTerm t
rInTerm (TermLet vs t) = any (\(VarBinding _ t') -> rInTerm t') vs || rInTerm t 

noVarInCmd :: Cmd -> Bool
noVarInCmd (SmtCmd (DefineFun _ _ _ t)) = noVarInTerm t
noVarInCmd _ = False

noVarInTerm :: Term -> Bool
noVarInTerm (TermIdent _) = False
noVarInTerm (TermLit _) = True
noVarInTerm (TermCall _ ts) = all noVarInTerm ts
noVarInTerm (TermExists _ t) = noVarInTerm t
noVarInTerm (TermForAll _ t) = noVarInTerm t
noVarInTerm (TermLet vs t) = all (\(VarBinding _ t') -> noVarInTerm t') vs && noVarInTerm t 

runCVC4Stream :: Int -> String -> IO (Either SomeException String)
runCVC4Stream max_size sygus =
    try (
        withSystemTempFile ("cvc4_input.sy")
            (\fp h -> do
                hPutStr h sygus
                -- We call hFlush to prevent hPutStr from buffering
                hFlush h

                (inp, outp, errp, _) <- P.runInteractiveCommand
                                            $ "cvc4 " ++ fp ++ " --lang=sygus2 --sygus-stream --sygus-abort-size=" ++ show max_size

                lnes <- readLines outp []

                hClose inp
                hClose outp
                hClose errp

                return lnes
            )
        )

readLines :: Handle -> [String] -> IO String
readLines h lnes = do
    b <- hIsEOF h
    if b
        then return . concat . reverse $ lnes
        else do
            lne <- hGetLine h
            if "(error" `isInfixOf` lne
                then readLines h lnes
                else readLines h (lne:lnes)

timeOutCommand :: IO String
timeOutCommand = do
    cmdMacOS <- findExecutable "gtimeout"
    case cmdMacOS of
        Just c -> return c
        Nothing -> return "timeout"