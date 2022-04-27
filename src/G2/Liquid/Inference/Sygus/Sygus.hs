{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.Inference.Sygus.Sygus where

import G2.Language as G2
import G2.Liquid.Interface
import G2.Liquid.Types
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.FuncConstraint
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.PolyRef
import G2.Liquid.Inference.Sygus.FCConverter
import G2.Liquid.Inference.Sygus.SpecInfo
import G2.Solver as Solver

import Sygus.LexSygus
import Sygus.ParseSygus
import Sygus.Print
import Sygus.Syntax as Sy

import Control.Monad.IO.Class 
import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Ratio
import qualified Data.Text as T

import Language.Haskell.Liquid.Types as LH hiding (SP, ms, isBool)

generateSygusProblem :: (InfConfigM m, ProgresserM m, MonadIO m) =>
                        [GhcInfo]
                     -> LiquidReadyState
                     -> Evals Bool
                     -> MeasureExs
                     -> FuncConstraints
                     -> ToBeNames
                     -> ToSynthNames
                     -> m [Cmd]
generateSygusProblem ghci lrs evals meas_ex fc to_be_ns ns_synth = do
    -- Figure out the type of each of the functions we need to synthesize
    let eenv = buildNMExprEnv $ expr_env . state $ lr_state lrs
        tenv = type_env . state $ lr_state lrs
        tc = type_classes . state $ lr_state lrs
        meas = lrsMeasures ghci lrs

    si <- buildSpecInfo eenv tenv tc meas ghci fc to_be_ns ns_synth

    let grammar = buildGrammars si

    let eval_ids = assignIds evals
        to_be_consts = createToBeConsts si eval_ids
    constraints <- constraintsToSygus eenv tenv meas meas_ex eval_ids si fc

    let cmds = [ SmtCmd (Sy.SetLogic "ALL")] ++ to_be_consts ++ grammar ++ constraints ++ [CheckSynth]

    liftIO $ putStrLn "-------------\nSyGuS\n"
    liftIO . putStrLn . T.unpack . printSygus $ cmds
    liftIO $ putStrLn "-------------"

    return cmds

-------------------------------
-- Grammar
-------------------------------

buildGrammars :: M.Map Name SpecInfo -> [Cmd]
buildGrammars =
    concatMap buildGrammars' . M.elems . M.filter (\si -> s_status si == Synth)

buildGrammars' :: SpecInfo -> [Cmd]
buildGrammars' si =
    map buildGrammars'' $ extractValues (s_syn_post si) ++ concatMap extractValues (s_syn_pre si)

buildGrammars'' :: SynthSpec -> Cmd
buildGrammars'' sy_spec =
    SynthFun (sy_name sy_spec)
             (map buildGramArgs $ sy_args_and_ret sy_spec)
             (IdentSort (ISymb "Bool"))
           . Just $ buildGrammar sy_spec

buildGramArgs :: SpecArg -> SortedVar
buildGramArgs sa = SortedVar (smt_var sa) (smtSortToSygusSort $ smt_sort sa)

buildGrammar :: SynthSpec -> GrammarDef
buildGrammar sy_spec =
    -- forceVarInGrammar (buildGramArgs $ sy_rets sy_spec)
    --                   (map buildGramArgs $ sy_args sy_spec)
                      (buildGrammar' sy_spec)

buildGrammar' :: SynthSpec -> GrammarDef
buildGrammar' sy_spec =
    GrammarDef 
        [ SortedVar "B" (IdentSort (ISymb "Bool"))
        , SortedVar "IConst" (IdentSort (ISymb "Int"))
        , SortedVar "I" (IdentSort (ISymb "Int"))]
        [ GroupedRuleList "B" (IdentSort (ISymb "Bool"))
            [ GVariable (IdentSort (ISymb "Bool"))
            , GConstant (IdentSort (ISymb "Bool"))
            , GBfTerm (BfIdentifierBfs (ISymb "=") [BfIdentifier (ISymb "I"), BfIdentifier (ISymb "I")])
            , GBfTerm (BfIdentifierBfs (ISymb ">") [BfIdentifier (ISymb "I"), BfIdentifier (ISymb "I")])
            , GBfTerm (BfIdentifierBfs (ISymb ">=") [BfIdentifier (ISymb "I"), BfIdentifier (ISymb "I")])
            ]
        , GroupedRuleList "IConst" (IdentSort (ISymb "Int"))
            [ GConstant (IdentSort (ISymb "Int")) ]
        , GroupedRuleList "I" (IdentSort (ISymb "Int"))
            [ GVariable (IdentSort (ISymb "Int"))
            , GConstant (IdentSort (ISymb "Int"))
            , GBfTerm (BfIdentifierBfs (ISymb "+") [BfIdentifier (ISymb "I"), BfIdentifier (ISymb "I")])
            , GBfTerm (BfIdentifierBfs (ISymb "*") [BfIdentifier (ISymb "IConst"), BfIdentifier (ISymb "I")])
            ]
        ]

-------------------------------
-- Constraints
-------------------------------

constraintsToSygus :: (InfConfigM m, ProgresserM m) =>
                      NMExprEnv
                   -> TypeEnv
                   -> Measures
                   -> MeasureExs
                   -> Evals (Integer, Bool)
                   -> M.Map Name SpecInfo
                   -> FuncConstraints
                   -> m [Cmd]
constraintsToSygus eenv tenv meas meas_ex evals si fc =
    return . map Constraint =<<
        convertConstraints 
                    convertExprToTerm
                    (ifNotNull mkSygusAnd (TermLit (LitBool True)))
                    (ifNotNull mkSygusOr (TermLit (LitBool False)))
                    mkSygusNot
                    mkSygusImplies
                    (\s -> TermCall (ISymb s))
                    (\_ _ -> TermLit . LitBool)
                    (\n i b ->
                        if b then
                            TermIdent (ISymb $ n ++ "__SYGUS_INT__" ++ show i)
                            else TermLit (LitBool False))
                    eenv tenv meas meas_ex evals si fc
    where
        ifNotNull _ def [] = def
        ifNotNull f _ xs = f xs

        mkSygusAnd = TermCall (ISymb "and") 
        mkSygusOr = TermCall (ISymb "or") 
        mkSygusNot t = TermCall (ISymb "not") [t]
        mkSygusImplies t1 t2 = TermCall (ISymb "=>") [t1, t2]

convertExprToTerm :: G2.Expr -> Term
convertExprToTerm (Data (DataCon (Name n _ _ _) _))
    | "True" <- n = TermLit $ LitBool True
    | "False" <- n =TermLit $ LitBool False
convertExprToTerm (Lit l) = litToTerm l
convertExprToTerm e = error $ "convertExprToTerm: Unhandled Expr " ++ show e

litToTerm :: G2.Lit -> Term
litToTerm (LitInt i) = TermLit (LitNum i)
litToTerm (LitDouble d) = TermCall (ISymb "/") [ TermLit . LitNum $ numerator d
                                               , TermLit . LitNum $ denominator d]
litToTerm (LitChar c) = TermLit (LitStr [c])
litToTerm _ = error "litToTerm: Unhandled Lit"

createToBeConsts :: M.Map Name SpecInfo -> Evals (Integer, Bool) -> [Cmd]
createToBeConsts si ev =
    let si' = M.mapKeys zeroOutName si in
       createToBeConsts' s_to_be_pre_name si' (pre_evals ev)
    ++ createToBeConsts' s_to_be_post_name si' (post_evals ev)
    where
      zeroOutName (Name n m _ l) = Name n m 0 l


createToBeConsts' :: (SpecInfo -> SMTName) ->  M.Map Name SpecInfo -> FCEvals ((Integer, Bool)) -> [Cmd]
createToBeConsts' f si = mapMaybe (createToBeConsts'' f si)
                       . concatMap (\(n, es) -> map (n,) es)
                       . HM.toList
                       . HM.map HM.elems

createToBeConsts'' :: (SpecInfo -> SMTName) -> M.Map Name SpecInfo -> (Name, (Integer, Bool)) -> Maybe Cmd
createToBeConsts'' f si (n, (i, _))
    | Just si' <- M.lookup n si
    , s_status si' == ToBeSynthed =
        Just $ DeclareVar (f si' ++ "__SYGUS_INT__" ++ show i) (IdentSort (ISymb "Bool"))
    | otherwise = Nothing

-------------------------------
-- Sorts
-------------------------------

smtSortToSygusSort :: Solver.Sort -> Sy.Sort
smtSortToSygusSort SortBool = IdentSort (ISymb "Bool")
smtSortToSygusSort SortInt = IdentSort (ISymb "Int")
smtSortToSygusSort s = error $ "smtSortToSygusSort: unsupported sort" ++ "\n" ++ show s

-------------------------------
-- Enforcing return value use
-------------------------------

-- Adjusts a grammar to force using a given GTerm

forceVarInGrammar :: SortedVar -- ^ The variable to force
                  -> [SortedVar]  -- ^ All other variables
                  -> GrammarDef
                  -> GrammarDef
forceVarInGrammar vr params (GrammarDef sv grls) =
    let
        prod_srt = mapMaybe (\grl@(GroupedRuleList grl_symb _ _) ->
                            if any (flip canProduceVar grl) (vr:params)
                                then Just grl_symb
                                else Nothing ) grls

        reach = gramSymbReachableFrom prod_srt grls

        sv_reach = concatMap (grammarDefSortedVars reach) sv

        (sv_final, grl_final) = elimNonTermGRL vr (forceVarInGRLList vr reach grls) sv_reach
    in
    GrammarDef sv_final grl_final

forceVarInGRLList :: SortedVar -> [Symbol] -> [GroupedRuleList] -> [GroupedRuleList]
forceVarInGRLList vr reach grls =
    let
        fv_map = HM.fromList $ map (\n -> (toBf n, toBf $ forcedVarSymb n)) reach

    in
    concatMap (forceVarInGRL vr reach fv_map) grls
    where
        toBf = BfIdentifier . ISymb

forceVarInGRL :: SortedVar -> [Symbol] -> HM.HashMap BfTerm BfTerm -> GroupedRuleList -> [GroupedRuleList]
forceVarInGRL (SortedVar sv_symb sv_srt) reach fv_map grl@(GroupedRuleList grl_symb grl_srt gtrms)
    | grl_symb `elem` reach =
        let
            bf_var = BfIdentifier (ISymb sv_symb)
            fv_gtrms' = if sv_srt == grl_srt
                                then GBfTerm bf_var:(filter (not . isClamp) $ elimVariable fv_gtrms)
                                else filter (not . isClamp) $ elimVariable fv_gtrms
        in
        [GroupedRuleList fv_symb grl_srt fv_gtrms', grl]
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

elimNonTermGRL :: SortedVar -> [GroupedRuleList] -> [SortedVar] -> ([SortedVar], [GroupedRuleList])
elimNonTermGRL (SortedVar sv_n _) grls sv =
    let
        has_term = hasTermFix (HS.singleton sv_n) grls

        sv' = filter (\(SortedVar n _) -> n `elem` has_term) sv
        grls' = map (elimRules has_term)
              $ filter (\(GroupedRuleList n _ _) -> n `elem` has_term) grls
    in
    (sv', grls')

hasTermFix :: HS.HashSet Symbol -> [GroupedRuleList] -> [Symbol]
hasTermFix ht grl =
    let
        ht' = HS.fromList
            . map (\(GroupedRuleList n _ _) -> n)
            $ filter (hasTermGRL ht) grl


        ht_all = HS.union ht ht'
    in
    if ht == ht_all then HS.toList ht_all else hasTermFix ht_all grl

hasTermGRL :: HS.HashSet Symbol -> GroupedRuleList -> Bool
hasTermGRL ht (GroupedRuleList n _ r) = n `HS.member` ht || any (hasTermGTerm ht) r

hasTermGTerm :: HS.HashSet Symbol -> GTerm -> Bool
hasTermGTerm _ (GConstant _) = True
hasTermGTerm _ (GVariable _) = True
hasTermGTerm ht (GBfTerm bft) = hasTermBfTerm ht bft

hasTermBfTerm :: HS.HashSet Symbol -> BfTerm -> Bool
hasTermBfTerm ht (BfIdentifier (ISymb i)) = i `HS.member` ht
hasTermBfTerm _ (BfLiteral _) = True
hasTermBfTerm ht (BfIdentifierBfs _ bfs) = all (hasTermBfTerm ht) bfs

isClamp :: GTerm -> Bool
isClamp (GBfTerm (BfIdentifier (ISymb "IClamp"))) = True
isClamp (GBfTerm (BfIdentifier (ISymb "DClamp"))) = True
isClamp _ = False

elimRules :: [Symbol] -> GroupedRuleList -> GroupedRuleList
elimRules grls (GroupedRuleList symb srt r) =
    GroupedRuleList symb srt $ filter (elimRules' grls) r

elimRules' :: [Symbol] -> GTerm -> Bool
elimRules' _ (GConstant _) = True
elimRules' _ (GVariable _) = True
elimRules' grls (GBfTerm bft) = elimRulesBfT grls bft

elimRulesBfT :: [Symbol] -> BfTerm -> Bool
elimRulesBfT grls (BfIdentifier (ISymb i)) = i `elem` grls
elimRulesBfT _ (BfLiteral _) = True
elimRulesBfT grls (BfIdentifierBfs _ bfs) = all (elimRulesBfT grls) bfs

-----------------------------------------------------

-- Substitution functions

substOnceGTerms :: HM.HashMap BfTerm BfTerm -> [GTerm] -> [GTerm]
substOnceGTerms m = concatMap (substOnceGTerm m)

substOnceGTerm :: HM.HashMap BfTerm BfTerm -> GTerm -> [GTerm]
substOnceGTerm m (GBfTerm bf) = map GBfTerm $ substOnceBfTerm m bf
substOnceGTerm _ gt = [gt]

substOnceBfTerm :: HM.HashMap BfTerm BfTerm -> BfTerm -> [BfTerm]
substOnceBfTerm m (BfIdentifierBfs c bfs) = elimRedundant . map (BfIdentifierBfs c) $ substsOnces m bfs
substOnceBfTerm _ bf = [bf]

elimRedundant :: [BfTerm] -> [BfTerm]
elimRedundant (b@(BfIdentifierBfs (ISymb s) [b1, b2]):xs) =
    let
        xs' = if isCommutative s
                then delete (BfIdentifierBfs (ISymb s) [b2, b1]) xs
                else xs
    in
    b:elimRedundant xs'
elimRedundant (x:xs) = x:elimRedundant xs
elimRedundant [] = []

isCommutative :: Symbol -> Bool
isCommutative "and" = True
isCommutative "=" = True
isCommutative "+" = True
isCommutative _ = False

-- | Given:
--      * A mapping of list element to be replaced, to new elements
--      * A list, xs
-- returns a list of new lists.  Each new list is xs, but with exactly one
-- occurence of an old element replaced by the corresponding new element.
substsOnces :: (Eq a, Hashable a) => HM.HashMap a a -> [a] -> [[a]]
substsOnces m = substsOnces' m []

substsOnces' :: (Eq a, Hashable a) => HM.HashMap a a -> [a] -> [a] -> [[a]]
substsOnces' _ _ [] = []
substsOnces' m rv (x:xs)
    | Just new <- HM.lookup x m = (reverse rv ++ new:xs):rst
    | otherwise = rst
        where
            rst = substsOnces' m (x:rv) xs

-----------------------------------------------------

grammarDefSortedVars :: [Symbol] -> SortedVar -> [SortedVar]
grammarDefSortedVars symbs sv@(SortedVar n srt)
    | n `elem` symbs = [SortedVar (forcedVarSymb n) srt, sv]
    | otherwise = [sv]

canProduceVar :: SortedVar -> GroupedRuleList -> Bool
canProduceVar vr@(SortedVar _ sv_srt) (GroupedRuleList _ grl_srt gtrms)
    | sv_srt == grl_srt = any (canProduceVarGTerm vr) gtrms
    | otherwise = False

canProduceVarGTerm :: SortedVar -> GTerm -> Bool
canProduceVarGTerm (SortedVar _ sv_srt) (GVariable gv_srt) = sv_srt == gv_srt
canProduceVarGTerm (SortedVar s _) (GBfTerm (BfIdentifier (ISymb is))) = s == is
canProduceVarGTerm s (GBfTerm (BfIdentifierBfs _ bfs)) = any (canProduceVarGTerm s) $ map GBfTerm bfs
canProduceVarGTerm _ (GBfTerm (BfLiteral _)) = False
canProduceVarGTerm _ (GConstant _) = False
canProduceVarGTerm _ t = error $ "Unhandled term" ++ show t

-----------------------------------------------------

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
containsSymbolIdent _ _ = False

