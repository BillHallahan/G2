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
import G2.Language.Typing
import G2.Liquid.Conversion
import G2.Liquid.Helpers
import G2.Liquid.Types
import G2.Liquid.Inference.FuncConstraint
import G2.Liquid.Inference.G2Calls

import Sygus.LexSygus
import Sygus.ParseSygus
import Sygus.Print
import Sygus.Syntax as Sy
import Language.Haskell.Liquid.Types as LH
import Language.Fixpoint.Types.Refinements as LH
import qualified Language.Fixpoint.Types as LH

import Control.Exception
import Data.Coerce
import Data.List
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T
import Data.Tuple
import System.Directory
import System.IO
import System.IO.Temp
import qualified System.Process as P

import Debug.Trace

refSynth :: SpecType -> G2.Expr -> Measures -> MeasureExs -> [FuncConstraint] -> MeasureSymbols -> IO LH.Expr
refSynth spc e meas meas_ex fc meas_sym = do
    print e
    print fc
    let sygus = printSygus $ sygusCall e meas meas_ex fc
    putStrLn . T.unpack $ sygus

    res <- runCVC4 (T.unpack sygus)

    case res of
        Left _ -> error "refSynth: Bad call to CVC4"
        Right res' -> do
            putStrLn . T.unpack $ sygus
            let smt_st = parse . lexSygus $ stripUnsat res'
                lh_st = refToLHExpr spc smt_st meas_sym

            print smt_st

            return lh_st

-------------------------------
-- Constructing Sygus Formula
-------------------------------

sygusCall :: G2.Expr -> Measures -> MeasureExs -> [FuncConstraint] -> [Cmd]
sygusCall e meas meas_ex fcs@(_:_) =
    let
        -- Figure out what measures we need to/can consider
        ty_e = PresType $ inTyForAlls (typeOf e)
        arg_ty_c = filter (not . isTYPE)
                 . filter (not . isLHDict)
                 $ argumentTypes ty_e
        ret_ty_c = returnType ty_e
        ty_c = arg_ty_c ++ [ret_ty_c]

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

        ts_applic_meas = trace ("dt_ts = " ++ show dt_ts ++ "\nmeas_ids' = " ++ show meas_ids') zip dt_ts meas_ids'

        sorts = typesToSort ts_applic_meas

        declare_dts = sortsToDeclareDTs sorts

        varN = map (\i -> "x" ++ show i) ([0..] :: [Integer])
        sortVars = map (uncurry SortedVar) . zip varN
                        . map (typeToSort sorts) . filter (not . isLHDict) $ rel_ty_c

        -- Converted constraints.  Measures cause us to lose information about the data, so after
        -- conversion we can have a constraint both postively and negatively.  We know that the postive
        -- constraint corresponds to an actual execution, so we keep that one, adnd drop the negative constraint.
        cons = map (termConstraints sorts meas_ex arg_ty_c ret_ty_c) fcs
        cons' = filterPosAndNegConstraints cons
        cons'' = map termConstraintToConstraint cons'

    in
    trace ("dt_ts = " ++ show dt_ts  ++"\napplic_meas' = " ++ show applic_meas' ++ "\nts = " ++ show sorts)
    [ SmtCmd (SetLogic "ALL")]
    ++
    declare_dts
    ++
    [SynthFun "refinement" sortVars boolSort (Just $ grammar sorts)]
    ++
    cons''
    ++
    [ CheckSynth ]
    where
        isLHDict e
            | (TyCon (Name n _ _ _) _):_ <- unTyApp e = n == "lh"
            | otherwise = False

        isPrimTy (TyCon (Name "Int" _ _ _) _) = True
        isPrimTy (TyCon (Name "Bool" _ _ _) _) = True
        isPrimTy _ = False
sygusCall _ _ _ _ = error "sygusCall: empty list"

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

grammar :: TypesToSorts -> GrammarDef
grammar sorts =
    let
        gramNames = zip (map (\i -> "G" ++ show i) ([0..] :: [Integer])) (allSortNames sorts)
        grams = map (\(g, s_symb) -> (g, IdentSort . ISymb $ s_symb)) gramNames
        sortsToGN = HM.fromList $ map swap gramNames

        brl = GroupedRuleList "B" boolSort
                (boolRuleList ++ addSelectors sortsToGN boolSort sorts)

        irl = GroupedRuleList "I" intSort
                (intRuleList ++ addSelectors sortsToGN intSort sorts)
    in
    GrammarDef
        ([ SortedVar "B" boolSort
         , SortedVar "I" intSort ]
         ++ map (uncurry SortedVar) grams)
        ([ brl
         , irl
         ]
         ++ map (uncurry dtGroupRuleList) grams) 

intRuleList :: [GTerm]
intRuleList =
    [ GVariable intSort
    , GConstant intSort
    , GBfTerm $ BfLiteral $ LitNum 0
    , GBfTerm $ BfIdentifierBfs (ISymb "+") [intBf, intBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "-") [intBf, intBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "*") [intBf, intBf]
    -- , GBfTerm $ BfIdentifierBfs (ISymb "mod") [intBf, intBf]
    ]

boolRuleList :: [GTerm]
boolRuleList =
    [ GVariable boolSort
    , GConstant boolSort
    , GBfTerm $ BfIdentifierBfs (ISymb "=") [intBf, intBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "<") [intBf, intBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "<=") [intBf, intBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "=>") [boolBf, boolBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "and") [boolBf, boolBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "or") [boolBf, boolBf]
    , GBfTerm $ BfIdentifierBfs (ISymb "not") [boolBf]
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

data TermConstraint = PosT { term_cons :: Term}
                    | NegT { term_cons :: Term}

termConstraints :: TypesToSorts -> MeasureExs -> [Type] -> Type -> FuncConstraint -> TermConstraint
termConstraints sorts meas_ex arg_tys ret_ty (Pos fc) =
    PosT $ funcCallTerm sorts meas_ex arg_tys ret_ty fc
termConstraints sorts meas_ex arg_tys ret_ty (Neg fc) =
    NegT $ funcCallTerm sorts meas_ex arg_tys ret_ty fc

funcCallTerm :: TypesToSorts -> MeasureExs -> [Type] -> Type -> FuncCall -> Term
funcCallTerm sorts meas_ex arg_tys ret_ty (FuncCall { arguments = ars, returns = r}) =
    let
        ars' = filter (not . isLhDict) . filter (not . isType) $ ars
    in
    TermCall (ISymb "refinement")
        (mapMaybe (uncurry (relExprToTerm sorts meas_ex)) (zip arg_tys ars') ++ [exprToTerm sorts meas_ex ret_ty r])
    where
        isType (Type _) = True
        isType _ = False

        isLhDict e
            | (Data (DataCon (Name n _ _ _) _)):_ <- unApp e = n == "lh"
            | otherwise = False

relExprToTerm :: TypesToSorts -> MeasureExs -> Type -> G2.Expr -> Maybe Term
relExprToTerm sorts meas_ex t e =
    if relTy t then Just $ exprToTerm sorts meas_ex t e else Nothing

exprToTerm :: TypesToSorts -> MeasureExs -> Type -> G2.Expr -> Term
exprToTerm _ _ (TyCon (Name "Bool" _ _ _) _) (Data (DataCon (Name n _ _ _) _))
    | "True" <- n = TermLit $ LitBool True
    | "False" <- n =TermLit $ LitBool False
exprToTerm _ _ (TyCon (Name n _ _ _) _) (App _ (Lit l))
    | n == "Int" || n == "Float" = litToTerm l
exprToTerm _ _ _ (Lit l) = litToTerm l
exprToTerm sorts meas_ex t e = exprToDTTerm sorts meas_ex t e
exprToTerm _ _ _ e = error $ "exprToTerm: Unhandled Expr " ++ show e

litToTerm :: G2.Lit -> Term
litToTerm (LitInt i) = TermLit (LitNum i)
litToTerm _ = error "litToTerm: Unhandled Lit"

filterPosAndNegConstraints :: [TermConstraint] -> [TermConstraint]
filterPosAndNegConstraints ts =
    let
        tre = filter isPosT ts
    in
    filter (\t -> isPosT t || all (\t' -> term_cons t /= term_cons t') tre ) ts
    where
        isPosT (PosT _) = True
        isPosT (NegT _) = False

termConstraintToConstraint :: TermConstraint -> Cmd
termConstraintToConstraint (PosT t) = Constraint t
termConstraintToConstraint (NegT t) = Constraint $ TermCall (ISymb "not") [t]

typeToSort :: TypesToSorts -> Type -> Sort
typeToSort _ (TyCon (Name n _ _ _) _) 
    | n == "Int" = intSort
    | n == "Bool" = boolSort
typeToSort sm t
    | Just si <- lookupSort t sm = IdentSort (ISymb $ sort_name si)
typeToSort _ t = error $ "Unknown Type " ++ show t

intBf :: BfTerm
intBf = BfIdentifier (ISymb "I")

boolBf :: BfTerm
boolBf = BfIdentifier (ISymb "B")

intSort :: Sort
intSort = IdentSort (ISymb "Int")

boolSort :: Sort
boolSort = IdentSort (ISymb "Bool")

nameToSymbol :: Name -> Symbol
nameToSymbol = nameToStr

exprToDTTerm :: TypesToSorts -> MeasureExs -> Type -> G2.Expr -> Term
exprToDTTerm sorts meas_ex t e =
    case lookupSort t sorts of
        Just si -> TermCall (ISymb (dt_name si)) $ map (measVal sorts meas_ex e) (meas_names si)
        Nothing -> error "exprToDTTerm: No sort found"

measVal :: TypesToSorts -> MeasureExs -> G2.Expr -> SortedVar -> Term
measVal sorts meas_ex e (SortedVar mn _) =
    let
        meas_n = strToName mn
    in
    case HM.lookup e meas_ex of
        Just meas_out
            |Just (_, v) <- find (\(n', _) -> nameOcc meas_n == nameOcc n') meas_out -> exprToTerm sorts meas_ex (typeOf v) v
        Nothing -> error "measVal: Expr not found"

-- | Is the given type usable by SyGuS?
relTy :: Type -> Bool
relTy (TyVar _) = False
relTy _ = True

-------------------------------
-- Measures
-------------------------------

newtype TypesToSorts = TypesToSorts { types_to_sorts :: [(Type, SortInfo)] }
                       deriving (Show, Read)

data SortInfo = SortInfo { sort_name :: Symbol
                         , dt_name :: Symbol
                         , meas_names :: [SortedVar]}
                         deriving (Show, Read)

typesToSort :: [(Type, [Id])] -> TypesToSorts
typesToSort ts =
    let
        ts_s = map (\(i, (t, ns)) -> typesToSort' i t ns) $ zip [0..] ts
    in
    TypesToSorts ts_s

typesToSort' :: Int -> Type -> [Id] -> (Type, SortInfo)
typesToSort' i t ns =
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
isPrimMeasure (Id _ t)
    | TyCon (Name "Int" _ _ _) _ <- t = True
    | TyCon (Name "Bool" _ _ _) _ <- t = True
    | otherwise = False

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

-------------------------------
-- Converting to refinement
-------------------------------

stripUnsat :: String -> String
stripUnsat ('u':'n':'s':'a':'t':xs) = xs
stripUnsat xs = xs

refToLHExpr :: SpecType -> [Cmd] -> MeasureSymbols -> LH.Expr
refToLHExpr st [SmtCmd cmd] meas_sym = refToLHExpr' st cmd meas_sym

refToLHExpr' :: SpecType -> SmtCmd -> MeasureSymbols -> LH.Expr
refToLHExpr' st (DefineFun _ ars _ trm) meas_sym =
    let
        ars' = map (\(SortedVar sym _) -> sym) ars

        symbs = specTypeSymbols st
        symbsArgs = M.fromList $ zip ars' symbs
    in
    termToLHExpr meas_sym symbsArgs trm

termToLHExpr :: MeasureSymbols -> M.Map Sy.Symbol LH.Symbol -> Term -> LH.Expr
termToLHExpr _ m_args (TermIdent (ISymb v)) =
    case M.lookup v m_args of
        Just v' -> EVar v'
        Nothing -> error "termToLHExpr: Variable not found"
termToLHExpr _ _ (TermLit l) = ECon (litToLHConstant l)
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
    -- | "mod" <- v
    -- , [t1, t2] <- ts = EBin LH.Mod (termToLHExpr meas_sym m_args t1) (termToLHExpr meas_sym m_args t2)
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
    error $ "v = " ++ show v ++ "\nmeas_syms' = " ++ show meas_sym'
termToLHExpr (_) _ t = error $ "termToLHExpr meas_sym m_args: unhandled " ++ show t

zeroName :: Name -> Name
zeroName (Name n m _ l) = Name n m 0 l

litToLHConstant :: Sy.Lit -> Constant
litToLHConstant (LitNum n) = I n

specTypeSymbols :: SpecType -> [LH.Symbol]
specTypeSymbols (RFun { rt_bind = b, rt_in = i, rt_out = out }) =
    case i of
        RVar {} -> specTypeSymbols out
        _ -> b:specTypeSymbols out
specTypeSymbols (RApp { rt_reft = ref }) = [reftSymbol $ ur_reft ref]
specTypeSymbols (RVar {}) = error "RVar"
specTypeSymbols (RAllT { rt_ty = out }) = specTypeSymbols out

reftSymbol :: Reft -> LH.Symbol
reftSymbol = fst . unpackReft

unpackReft :: Reft -> (LH.Symbol, LH.Expr) 
unpackReft = coerce

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
