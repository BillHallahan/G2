{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.RefSynth (refSynth) where

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax as G2
import G2.Language.Typing
import G2.Liquid.Inference.FuncConstraint
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.PolyRef

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
import qualified Data.Text as T
import Data.Tuple
import System.Directory
import System.IO
import System.IO.Temp
import qualified System.Process as P

refSynth :: SpecType -> MeasureExs -> [FuncConstraint] -> IO LH.Expr
refSynth spec meas_ex fc = do
    putStrLn $ "fc = " ++ show fc
    putStrLn $ "extractPolyBound fc = "
                ++ show (map (map extractPolyBound . arguments . constraint) $ fc)

    putStrLn $ "meas_ex = " ++ show meas_ex
    putStrLn $ "repArgsWithPrims . filterMeasureExs $ meas_ex = " ++ show (fst . repArgsWithPrims . filterMeasureExs $ meas_ex)

    let sygus = printSygus $ sygusCall meas_ex fc
    print sygus

    res <- runCVC4 $ T.unpack sygus

    case res of
        Left _ -> error "refSynth: Bad call to CVC4"
        Right res' -> do
            putStrLn . T.unpack $ sygus
            let smt_st = parse . lexSygus $ stripUnsat res'
                lh_st = refToLHExpr spec smt_st

            print smt_st

            return lh_st

-------------------------------
-- Constructing Sygus Formula
-------------------------------

sygusCall :: MeasureExs -> [FuncConstraint] -> [Cmd]
sygusCall meas_ex fcs@(fc:_) =
    let
        (meas_ex', sort_map) = repArgsWithPrims . filterMeasureExs $ meas_ex
        expr_dt_map = exprToDTMap sort_map

        declare_dts = sortMapToDeclareDTs sort_map
        meas_funs = measuresToDefineFuns meas_ex'

        ts = map typeOf (arguments $ constraint fc) ++ [typeOf (returns $ constraint fc)]

        varN = map (\i -> "x" ++ show i) ([0..] :: [Integer])
        sortVars = map (uncurry SortedVar) . zip varN $ map (typeToSort sort_map) ts
    in
    [ SmtCmd (SetLogic "ALL")]
    ++
    map SmtCmd declare_dts
    ++
    map SmtCmd meas_funs
    ++
    [SynthFun "refinement" sortVars boolSort (Just $ grammar meas_ex' sort_map) ]
    ++
    map (constraints expr_dt_map) fcs
    ++
    [ CheckSynth ]
sygusCall _ _ = error "sygusCall: empty list"

grammar :: TMeasureExs -> SortMap -> GrammarDef
grammar meas_ex sort_map =
    let
        sorts = map dt_name $ HM.elems sort_map
        gramNames = zip (map (\i -> "G" ++ show i) [0..]) $ map (IdentSort . ISymb) sorts
        sortsToGN = HM.fromList $ map swap gramNames

        boolRuleList =
            GroupedRuleList "B" boolSort 
                ([ GVariable boolSort
                 , GConstant boolSort
                 , GBfTerm $ BfIdentifierBfs (ISymb "=") [intBf, intBf]
                 , GBfTerm $ BfIdentifierBfs (ISymb "<") [intBf, intBf]
                 , GBfTerm $ BfIdentifierBfs (ISymb "=>") [boolBf, boolBf]
                 , GBfTerm $ BfIdentifierBfs (ISymb "and") [boolBf, boolBf]
                 , GBfTerm $ BfIdentifierBfs (ISymb "or") [boolBf, boolBf]
                 , GBfTerm $ BfIdentifierBfs (ISymb "not") [boolBf]
                 ]
                 ++ measureExsToGTerm sortsToGN boolSort meas_ex)

        intRuleList =
            GroupedRuleList "I" intSort 
                ([ GVariable intSort
                 , GConstant intSort
                 , GBfTerm $ BfIdentifierBfs (ISymb "+") [intBf, intBf]
                 , GBfTerm $ BfIdentifierBfs (ISymb "-") [intBf, intBf]
                 , GBfTerm $ BfIdentifierBfs (ISymb "*") [intBf, intBf]
                 -- , GBfTerm $ BfIdentifierBfs (ISymb "mod") [intBf, intBf]
                 ]
                 ++ measureExsToGTerm sortsToGN intSort meas_ex)
    in
    GrammarDef
        ([ SortedVar "B" boolSort
         , SortedVar "I" intSort ]
         ++ map (uncurry SortedVar) gramNames)
        ([ boolRuleList
         , intRuleList
         ]
         ++ map (uncurry dtGroupRuleList) gramNames) 

dtGroupRuleList :: Symbol -> Sort -> GroupedRuleList
dtGroupRuleList symb srt = GroupedRuleList symb srt [GVariable srt]

constraints :: ExprDTMap -> FuncConstraint -> Cmd
constraints edtm (Pos fc) =
    Constraint $ TermCall (ISymb "=") [funcCallTerm edtm fc, TermLit (LitBool True)]
constraints edtm (Neg fc) =
    Constraint $ TermCall (ISymb "=") [funcCallTerm edtm fc, TermLit (LitBool False)]

funcCallTerm :: ExprDTMap ->  FuncCall -> Term
funcCallTerm edtm (FuncCall { arguments = args, returns = r}) =
    TermCall (ISymb "refinement") (map (exprToTerm edtm) args ++ [exprToTerm edtm r])

exprToTerm :: ExprDTMap -> G2.Expr -> Term
exprToTerm _ (App _ (Lit l)) = litToTerm l
exprToTerm _ (Lit l) = litToTerm l
exprToTerm edtm e
    | Just (sym, _) <- HM.lookup e edtm = TermIdent (ISymb sym)
exprToTerm _ e = error $ "exprToTerm: Unhandled Expr " ++ show e

litToTerm :: G2.Lit -> Term
litToTerm (LitInt i) = TermLit (LitNum i)
litToTerm _ = error "litToTerm: Unhandled Lit"

typeToSort :: SortMap -> Type -> Sort
typeToSort _ (TyCon n@(Name n' _ _ _) _) 
    | n' == "Int" = intSort
    | n' == "Bool" = boolSort
typeToSort sm t
    | Just (DTInfo { dt_name = srt }) <- HM.lookup t sm = IdentSort (ISymb srt)
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

-------------------------------
-- Measures
-------------------------------

type TMeasureExs = GMeasureExs (Term, Sort)
type TMeasureEx = GMeasureEx (Term, Sort)

data DTInfo = DTInfo { dt_name :: Symbol
                     , dt_cons :: [(G2.Expr, Symbol, Sort)] }

type SortMap = HM.HashMap Type DTInfo

type ExprDTMap = HM.HashMap G2.Expr (Symbol, Sort)

measuresToDefineFuns :: TMeasureExs -> [SmtCmd]
measuresToDefineFuns =
    map (uncurry measuresToDefineFuns') . HM.toList . HM.map (HS.toList)

measuresToDefineFuns' :: Name -> [TMeasureEx] -> SmtCmd
measuresToDefineFuns' n me@(m:_) =
    let
        svSymb = "x"
        sv = SortedVar svSymb (snd $ meas_in m)
        tm = measureExToIte svSymb me
    in
    DefineFun (nameToSymbol n) [sv] intSort tm
measuresToDefineFuns' _ [] = error "measuresToDefineFuns': Empty list"

measureExToIte :: Symbol -> [TMeasureEx] -> Term
measureExToIte b (m:[]) = fst . meas_out $ m
measureExToIte b (m:ms) =
    let
        t_in = fst . meas_in $ m
        t_out = fst . meas_out $ m
        t_eq = TermCall (ISymb "=") [TermIdent (ISymb b), t_in]
    in
    TermCall (ISymb "ite") [t_eq, t_out, measureExToIte b ms]
measureExToIte b [] = error "measureExToIte: Empty list"

sortMapToDeclareDTs :: SortMap -> [SmtCmd]
sortMapToDeclareDTs = map dtInfoToDeclareDT . HM.elems

dtInfoToDeclareDT :: DTInfo -> SmtCmd
dtInfoToDeclareDT (DTInfo { dt_name = n, dt_cons = cons}) =
    DeclareDatatype n . DTDec $ map (\(_, c, _) -> DTConsDec c []) cons

measureExsToGTerm :: HM.HashMap Sort Symbol -> Sort -> TMeasureExs -> [GTerm]
measureExsToGTerm sortToGram srt =
    map (uncurry (measureExToGTerm sortToGram)) . HM.toList . filterByReturnSort srt

filterByReturnSort :: Sort -> TMeasureExs -> TMeasureExs
filterByReturnSort srt = HM.filter (not . HS.null) . HM.map (HS.filter (filterByReturnSort' srt))

filterByReturnSort' :: Sort -> TMeasureEx -> Bool
filterByReturnSort' srt (MeasureEx { meas_out = (_, srt')}) = srt == srt'

measureExToGTerm :: HM.HashMap Sort Symbol -> Name -> HS.HashSet TMeasureEx -> GTerm
measureExToGTerm sortToGram f meas_ex
    | (MeasureEx { meas_in = (_, srt) }:_) <- HS.toList meas_ex
    , Just g <- HM.lookup srt sortToGram =
    GBfTerm $ BfIdentifierBfs (ISymb (nameToSymbol f)) [BfIdentifier (ISymb g)]
measureExToGTerm _ _ _ = error "measureExToGTerm: Unknown sort or empty set"

-- | Replaces the arguments in a `MeasureExs` with primitives, and returns both the
-- new `MeasureExs`, and a `HashMap` to map the arguments to the primitives.
repArgsWithPrims :: MeasureExs -> (TMeasureExs, SortMap)
repArgsWithPrims meas_ex =
    let
        ars = map meas_in . HS.toList . HS.unions $ HM.elems meas_ex
        tyArgs = [ (t, filter (.:: t) ars) | t <- nub $ map typeOf ars]

        sort_map = tyArgsToSortMap tyArgs
        expr_to_dt = exprToDTMap sort_map
    in
    (measureExsToTMeasureExs sort_map expr_to_dt meas_ex, sort_map)

tyArgsToSortMap :: [(Type, [G2.Expr])] -> SortMap
tyArgsToSortMap = HM.fromList . tyArgsToSortMap' . zip [0..]

tyArgsToSortMap' :: [(Int, (Type, [G2.Expr]))] -> [(Type, DTInfo)]
tyArgsToSortMap' [] = []
tyArgsToSortMap' ((n, (t, es)):tes) = (t, toDTInfo n t es):tyArgsToSortMap' tes

toDTInfo :: Int -> Type -> [G2.Expr] -> DTInfo
toDTInfo n t es =
    let
        sort_name = "DTS" ++ show n
    in
    DTInfo { dt_name = sort_name
           , dt_cons = map (uncurry (toDTCons sort_name n)) $ zip [0..] es}

toDTCons :: Symbol -> Int -> Int -> G2.Expr -> (G2.Expr, Symbol, Sort)
toDTCons sn n n' e = (e, "DT" ++ show n ++ "_" ++ show n', IdentSort (ISymb sn))

measureExsToTMeasureExs :: SortMap -> ExprDTMap -> MeasureExs -> TMeasureExs
measureExsToTMeasureExs sort_map esm = HM.map (HS.map (measureExToTMeasureEx sort_map esm))

measureExToTMeasureEx :: SortMap -> ExprDTMap -> MeasureEx -> TMeasureEx
measureExToTMeasureEx sort_map esm (MeasureEx { meas_in = m_in, meas_out = m_out })
    | Just (m_in', s_in) <- HM.lookup m_in esm =
        MeasureEx { meas_in = (TermIdent $ ISymb m_in', s_in)
                  , meas_out = (exprToTerm esm m_out, typeToSort sort_map (typeOf m_out)) }
    | otherwise = error "measureExToTMeasureEx: Failed lookup"


exprToDTMap :: SortMap -> ExprDTMap
exprToDTMap = HM.fromList . map (\(e, sym, srt) -> (e, (sym, srt))) . concatMap dt_cons . HM.elems

filterMeasureExs :: MeasureExs -> MeasureExs
filterMeasureExs = filterErrors . filterNonPrimsMeasureExs

-- | Eliminates measures where any of the returned values is Error
filterErrors :: MeasureExs -> MeasureExs
filterErrors = HM.filter (all (not . isErrorReturns) . HS.toList)

filterNonPrimsMeasureExs :: MeasureExs -> MeasureExs
filterNonPrimsMeasureExs = HM.filter (not . HS.null) . HM.map (HS.filter isPrimReturns)

-- | Eliminates measures that do not return primitives
isPrimReturns :: MeasureEx -> Bool
isPrimReturns (MeasureEx { meas_out = App (Data (DataCon n _)) _ }) = nameOcc n == "I#"
isPrimReturns (MeasureEx { meas_out = Prim Error _ }) = True
isPrimReturns _ = False

isErrorReturns :: MeasureEx -> Bool
isErrorReturns (MeasureEx { meas_out = Prim Undefined _ }) = True
isErrorReturns (MeasureEx { meas_out = Prim Error _ }) = True
isErrorReturns _ = False

-------------------------------
-- Converting to refinement
-------------------------------

stripUnsat :: String -> String
stripUnsat ('u':'n':'s':'a':'t':xs) = xs
stripUnsat xs = xs

refToLHExpr :: SpecType -> [Cmd] -> LH.Expr
refToLHExpr st [SmtCmd cmd] = refToLHExpr' st cmd

refToLHExpr' :: SpecType -> SmtCmd -> LH.Expr
refToLHExpr' st (DefineFun _ args _ trm) =
    let
        args' = map (\(SortedVar sym _) -> sym) args

        symbs = specTypeSymbols st
        symbsArgs = M.fromList $ zip args' symbs
    in
    termToLHExpr symbsArgs trm

termToLHExpr :: M.Map Sy.Symbol LH.Symbol -> Term -> LH.Expr
termToLHExpr m (TermIdent (ISymb v)) =
    case M.lookup v m of
        Just v' -> EVar v'
        Nothing -> error "termToLHExpr: Variable not found"
termToLHExpr _ (TermLit l) = ECon (litToLHConstant l)
termToLHExpr m (TermCall (ISymb v) ts)
    -- EBin
    | "+" <- v
    , [t1, t2] <- ts = EBin LH.Plus (termToLHExpr m t1) (termToLHExpr m t2)
    | "-" <- v
    , [t1] <- ts = ENeg (termToLHExpr m t1)
    | "-" <- v
    , [t1, t2] <- ts = EBin LH.Minus (termToLHExpr m t1) (termToLHExpr m t2)
    | "*" <- v
    , [t1, t2] <- ts = EBin LH.Times (termToLHExpr m t1) (termToLHExpr m t2)
    -- | "mod" <- v
    -- , [t1, t2] <- ts = EBin LH.Mod (termToLHExpr m t1) (termToLHExpr m t2)
    -- More EBin...
    | "and" <- v = PAnd $ map (termToLHExpr m) ts
    | "or" <- v = POr $ map (termToLHExpr m) ts
    | "not" <- v, [t1] <- ts = PNot (termToLHExpr m t1)
    -- PAtom
    | "=" <- v
    , [t1, t2] <- ts = PAtom LH.Eq (termToLHExpr m t1) (termToLHExpr m t2)
    | ">" <- v 
    , [t1, t2] <- ts = PAtom LH.Gt (termToLHExpr m t1) (termToLHExpr m t2)
     | ">=" <- v 
    , [t1, t2] <- ts = PAtom LH.Ge (termToLHExpr m t1) (termToLHExpr m t2)
    | "<" <- v 
    , [t1, t2] <- ts = PAtom LH.Lt (termToLHExpr m t1) (termToLHExpr m t2)
   | "<=" <- v 
    , [t1, t2] <- ts = PAtom LH.Le (termToLHExpr m t1) (termToLHExpr m t2)
    -- More PAtom...
termToLHExpr _ t = error $ "termToLHExpr: unhandled " ++ show t

litToLHConstant :: Sy.Lit -> Constant
litToLHConstant (LitNum n) = I n

specTypeSymbols :: SpecType -> [LH.Symbol]
specTypeSymbols (RFun { rt_bind = b, rt_out = out }) = b:specTypeSymbols out
specTypeSymbols (RApp { rt_reft = ref }) = [reftSymbol $ ur_reft ref]
specTypeSymbols (RVar {}) = error "RVar"
specTypeSymbols (RAllT {}) = error "RAllT"

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

            P.readProcess toCommand ["10", "cvc4", fp, "--lang=sygus2"] "")
        )