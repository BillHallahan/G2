{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.QualifGen (qualifGen) where

import G2.Language.Naming
import G2.Liquid.Inference.RefSynth
import G2.Liquid.Helpers

import Sygus.LexSygus
import Sygus.ParseSygus
import Sygus.Print
import Sygus.Syntax

import Language.Fixpoint.Types.Constraints
import qualified Language.Fixpoint.Types.Names as LH
import Language.Fixpoint.Types.PrettyPrint

import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T
import Data.Tuple

-- | Mocking measures to generate Qualifs.
data QMeasure = QMeasure { m_name :: String
                         , m_in :: Sort
                         , m_out :: Sort
                         , triv_out :: Term }

-- Mocking datatypes
data QDataType = QDataType { dt_smt_name :: String
                           , dt_name :: String
                           , dt_cons :: [String] }

data QualifConfig = QualifConfig { max_vars :: Int
                                 , max_size :: Int
                                 , datatypes :: [QDataType]
                                 , measures :: [QMeasure] }

qualifGen :: FilePath -> IO ()
qualifGen qualif_fp = do
    let qc = QualifConfig 
                { max_vars = 3
                , max_size = 5
                , datatypes = [ QDataType { dt_smt_name = "List"
                                          , dt_name = "ListQualif.List a"
                                          , dt_cons = ["cons", "nil"] }
                              , QDataType { dt_smt_name = "List_List"
                                          , dt_name = "ListQualif.List (ListQualif.List b)"
                                          , dt_cons = ["cons_cons", "nil_nil"] }]
                , measures =
                    [ QMeasure { m_name = "size_m__0"
                               , m_in = listSort
                               , m_out = intSort
                               , triv_out = trivOutGen (TermIdent (ISymb "cons"))
                                                       (TermLit $ LitNum 0)
                                                       (TermLit $ LitNum 2000)
                               }
                    , QMeasure { m_name = "sizeXs_m__0"
                               , m_in = IdentSort (ISymb "List_List")
                               , m_out = intSort
                               , triv_out = trivOutGen (TermIdent (ISymb "cons_cons"))
                                                       (TermLit $ LitNum 0)
                                                       (TermLit $ LitNum 4000)
                               }
                    ]
                }

    cmds <- qualifCalls qc

    let printable_quals = map (cmdToQualifs (datatypes qc) (measures qc)) cmds
    
    writeFile qualif_fp (intercalate "\n" printable_quals)

trivOutGen :: Term -> Term -> Term -> Term
trivOutGen v t1 t2 =
    TermCall (ISymb "ite") 
        [TermCall (ISymb "=") [TermIdent (ISymb "a"), v], t1, t2]

qualifCalls :: QualifConfig -> IO [Cmd]
qualifCalls (QualifConfig { max_vars = max_v
                          , max_size = max_s
                          , datatypes = dt
                          , measures = meas }) = do

    let srtss = concatMap (flip combinations (possibleDTs dt)) [1..max_v]

    r <- mapM (\srts -> do
            let varN = map (\i -> "x" ++ show i) ([0..] :: [Int])
                svs = map (uncurry SortedVar) $ zip varN srts

            let call = qualifCalls' dt meas svs
            putStrLn . T.unpack $ printSygus call
            res <- runCVC4Stream max_s . T.unpack $ printSygus call

            case res of
                Left err -> error "qualifGen: Bad call to CVC4"
                Right res' -> do
                    let p_res = parse . lexSygus $ res'
                        all_used_res = filter defineFunAllUsed p_res

                    return all_used_res
         ) srtss

    return $ concat r

combinations :: Int -> [a] -> [[a]]
combinations 0 _ = [[]]
combinations !n xs = [x:ys | x <- xs, ys <- combinations (n - 1) xs]

possibleDTs :: [QDataType] -> [Sort]
possibleDTs dts =
    let
        srts = map (IdentSort . ISymb . dt_smt_name) dts
    in
    [intSort, boolSort] ++ srts

qualifCalls' :: [QDataType] -> [QMeasure] -> [SortedVar] -> [Cmd]
qualifCalls' q_dt q_meas sortVars =
    let
        dt_srts = filter (\s -> s /= intSort && s /= boolSort)
                    . nub . map (\(SortedVar _ s) -> s) $ sortVars
        
        gram_names = zip (map (\i -> "G" ++ show i) [0..]) dt_srts

        gram = qualifGrammar gram_names q_meas
        gram' = filterGrammar gram
    in
    [ SmtCmd (SetLogic "ALL")]
    ++
    map qDataTypeToDeclareDataType q_dt
    ++
    map qMeasureToDefineFun q_meas
    ++
    [SynthFun "qualif" sortVars boolSort (Just gram')]
    ++
    [ CheckSynth ]

qualifGrammar :: [(String, Sort)] -> [QMeasure] -> GrammarDef
qualifGrammar dt_gram_names meas =
    let
        sw_gram_names = map swap dt_gram_names

        brl = GroupedRuleList "B" boolSort
            (boolRuleList ++ qualifGramMeasCalls boolSort sw_gram_names meas)
        irl = GroupedRuleList "I" intSort
                (intRuleList ++ qualifGramMeasCalls intSort sw_gram_names meas)

        dt_rule_lists = map (\(gn, s) -> GroupedRuleList gn s [GVariable s]) dt_gram_names
    in
    GrammarDef
        ([ SortedVar "B" boolSort
         , SortedVar "I" intSort ]
         ++ map (uncurry SortedVar) dt_gram_names)
        ([brl, irl] ++ dt_rule_lists)

qualifGramMeasCalls :: Sort -> [(Sort, String)] -> [QMeasure] -> [GTerm]
qualifGramMeasCalls srt sort_to_gram = mapMaybe (qualifGramMeasCall srt sort_to_gram)

qualifGramMeasCall :: Sort -> [(Sort, String)] -> QMeasure -> Maybe GTerm
qualifGramMeasCall srt sort_to_gram meas@(QMeasure { m_name = f, m_in = i, m_out = out })
    | srt == out
    , Just g <- lookup i sort_to_gram =
        Just . GBfTerm $ BfIdentifierBfs (ISymb f) [BfIdentifier (ISymb g)]
    | otherwise = Nothing

-- | Eliminates or replaces the constant commands to avoid infinite grammars.
-- Eliminates And, since we get that anyway with Qualifs approach
filterGrammar :: GrammarDef -> GrammarDef
filterGrammar (GrammarDef sv grl) = GrammarDef sv $ map filterGrammar' grl

filterGrammar' :: GroupedRuleList -> GroupedRuleList
filterGrammar' (GroupedRuleList symb srt gterms) =
    GroupedRuleList symb srt . filter (not . isAnd) $ filter (not . isConstant) gterms

isConstant :: GTerm -> Bool
isConstant (GConstant _) = True
isConstant _ = False

isAnd :: GTerm -> Bool
isAnd (GBfTerm (BfIdentifierBfs (ISymb "and") _)) = True
isAnd _ = False

-- | Converts a QDataType to a declare-datatype
qDataTypeToDeclareDataType :: QDataType -> Cmd
qDataTypeToDeclareDataType q_dt =
    SmtCmd . DeclareDatatype (dt_smt_name q_dt)
            . DTDec . map (flip DTConsDec []) $ dt_cons q_dt 

-- | Converts a QMeasure to a define-fun
qMeasureToDefineFun :: QMeasure -> Cmd
qMeasureToDefineFun q_meas =
    let
        ar = SortedVar "a" (m_in q_meas)
    in
    SmtCmd $ DefineFun (m_name q_meas) [ar] (m_out q_meas) (triv_out q_meas)

-- | Returns True if given an SMT define fun command that uses all it's arguments.  False otherwise
defineFunAllUsed :: Cmd -> Bool
defineFunAllUsed (SmtCmd (DefineFun _ sv _ t)) = allVariablesUsed sv t
defineFunAllUsed _ = False

-- | Returns true if all the variable are used in the Term.  False otherwise. 
allVariablesUsed :: [SortedVar] -> Term -> Bool
allVariablesUsed svs t =
    let
        vs = map (\(SortedVar i _) -> ISymb i) svs
        used = usedIdentifiers t
    in
    vs \\ used == []

usedIdentifiers :: Term -> [Identifier]
usedIdentifiers (TermIdent ind) = [ind]
usedIdentifiers (TermLit _) = []
usedIdentifiers (TermCall _ ts) = mconcat $ map usedIdentifiers ts
usedIdentifiers (TermExists _ t) = usedIdentifiers t
usedIdentifiers (TermForAll _ t) = usedIdentifiers t
usedIdentifiers (TermLet vb t) = concatMap usedInVarBindings vb ++ usedIdentifiers t

usedInVarBindings :: VarBinding -> [Identifier]
usedInVarBindings (VarBinding _ t) = usedIdentifiers t

cmdToQualifs :: [QDataType] -> [QMeasure] -> Cmd -> String
cmdToQualifs dts meas (SmtCmd (DefineFun _ sv _ t)) =
    let
        sv_str = map sortedVarSymbol sv
        sv_to_symb = M.fromList . zip sv_str $ map LH.symbol sv_str

        meas_names = map (nameOcc . strToName . m_name) meas

        lh_expr = termToLHExpr (MeasureSymbols $ map LH.symbol meas_names) sv_to_symb t
        lh_expr_str = map (\c -> if c == '\n' then ' ' else c) $ show (pprintTidy Full lh_expr)
    in
    "qualif Qualif(" ++ bindSortedVars dts sv ++ ") : (" ++ lh_expr_str ++ ")"

sortedVarSymbol :: SortedVar -> Symbol
sortedVarSymbol (SortedVar v _) = v

bindSortedVars :: [QDataType] -> [SortedVar] -> String
bindSortedVars dts = intercalate ", " . map (bindSortedVar dts)

bindSortedVar :: [QDataType] -> SortedVar -> String
bindSortedVar dts (SortedVar v srt) = v ++ ":" ++ sortString dts srt

sortString :: [QDataType] -> Sort -> String
sortString dts (IdentSort (ISymb s))
    | Just dt <- find (\d -> s == dt_smt_name d) dts = dt_name dt
    | otherwise = s
sortString _ _ = error "sortString: Unexpected sort"


-------------------------------
-- Various specific sorts
-------------------------------

listSort :: Sort
listSort = IdentSort (ISymb "List")
