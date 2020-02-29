{-# LANGUAGE LambdaCase #-}

module G2.Liquid.Inference.SimplifySygus ( EliminatedSimple
                                         , elimSimpleDTs
                                         , restoreSimpleDTs ) where

import Sygus.Syntax

import Data.Coerce
import Data.List
import qualified Data.HashMap.Lazy as M
import Data.Maybe
import qualified Data.Set as S

-- | Maps a tuple of a (1) function name and (2) function param to selector calls and variables
-- with ADTs sorts
data EliminatedSimple = EliminatedSimple { func_args :: M.HashMap Symbol [SortedVar]
                                         , vars_to_terms :: M.HashMap (Symbol, Symbol) Term }

emptyES :: EliminatedSimple
emptyES = EliminatedSimple M.empty M.empty

insertArgsES :: Symbol -> [SortedVar] -> EliminatedSimple -> EliminatedSimple
insertArgsES fn sv es = es { func_args = M.insert fn sv (func_args es) }

insertTermES :: (Symbol, Symbol) -> Term -> EliminatedSimple -> EliminatedSimple
insertTermES fn_p t es = es { vars_to_terms = M.insert fn_p t (vars_to_terms es) }

lookupArgsES :: Symbol -> EliminatedSimple -> Maybe [SortedVar]
lookupArgsES fn = M.lookup fn . func_args

lookupTermES :: (Symbol, Symbol) -> EliminatedSimple -> Maybe Term
lookupTermES fn_p = M.lookup fn_p . vars_to_terms

selectorToVar :: Symbol -> Symbol -> EliminatedSimple -> Maybe Symbol
selectorToVar fn tn =
    fmap (\((_, v), _) -> v)
    . listToMaybe
    . filter (\((fn', _), t) ->
                    case t of
                        TermCall (ISymb tn') _ -> fn == fn' && tn == tn'
                        _ -> False
             )
    . M.toList
    . vars_to_terms

-----------------------------------------

-- | We define a simple datatype as a datatype that exists only as a wrapper on primitive datatypes
-- This function takes a SyGuS problem containing simple datatypes, and eliminates them.
-- It also returns a mapping, which can be used by `restoreSimpleDTs`, to bring back those datatypes
-- in a solution.
elimSimpleDTs :: [Cmd] -> (EliminatedSimple, [Cmd])
elimSimpleDTs cmds =
    let
        simple_srts = getSimpleSorts cmds
    in
    mapAccumL (elimSimpleDTs' simple_srts) emptyES cmds

elimSimpleDTs' :: M.HashMap Symbol (Symbol, [SortedVar]) -> EliminatedSimple -> Cmd -> (EliminatedSimple, Cmd)
elimSimpleDTs' simple_srts es (Constraint t) = (es, Constraint $ elimSimpleDTsTerms simple_srts t)
elimSimpleDTs' _ _ (InvConstraint _ _ _ _) = error "elimSimpleDTs': InvConstraint unsupported"
elimSimpleDTs' simple_srts es (SynthFun fn sv rs (Just gd)) =
    let
        (es', sv') = mapAccumL (elimSimpleDTsSVs fn simple_srts) es sv
        es'' = insertArgsES fn sv es'
        sv'' = concat sv'

        gd' = adjustSimpleInGrammar simple_srts fn es' gd
    in
    (es'', SynthFun fn sv'' rs (Just gd'))
elimSimpleDTs' _ es cmd = (es, cmd)

elimSimpleDTsSVs :: Symbol -> M.HashMap Symbol (Symbol, [SortedVar]) -> EliminatedSimple -> SortedVar -> (EliminatedSimple, [SortedVar])
elimSimpleDTsSVs fn simple_srts es sv@(SortedVar symb srt)
    | IdentSort (ISymb isrt) <- srt
    , Just (dt, params) <- M.lookup isrt simple_srts =
        let
            new_sv = map (\(SortedVar n i) -> SortedVar (symb ++ "__" ++ n) i) params
            es' = foldr (\(SortedVar n i) -> insertTermES (fn, symb ++ "__" ++ n) (TermCall (ISymb n) [TermIdent (ISymb symb)])) es params
        in
        (es', new_sv)
    | otherwise = (es, [sv])

elimSimpleDTsTerms :: M.HashMap Symbol (Symbol, [SortedVar]) -> Term -> Term
elimSimpleDTsTerms _ t@(TermIdent _) = t
elimSimpleDTsTerms _ t@(TermLit _) = t
elimSimpleDTsTerms simple_srts t@(TermCall i ts) =
    TermCall i . map (elimSimpleDTsTerms simple_srts) $ concatMap (elimSimpleDTsList simple_srts) ts
elimSimpleDTsTerms _ t = error $ "elimSimpleDTsTerms: Unhandled term " ++ show t

elimSimpleDTsList :: M.HashMap Symbol (Symbol, [SortedVar]) -> Term -> [Term]
elimSimpleDTsList _ t@(TermIdent _) = [t]
elimSimpleDTsList _ t@(TermLit _) = [t]
elimSimpleDTsList simple_srts t@(TermCall (ISymb s) ts)
    | s `S.member` getSimpleDTs simple_srts = ts
    | otherwise = [t]
elimSimpleDTsList _ t = error $ "elimSimpleDTsList: Unhandled term " ++ show t

adjustSimpleInGrammar :: M.HashMap Symbol (Symbol, [SortedVar]) -> Symbol -> EliminatedSimple -> GrammarDef -> GrammarDef
adjustSimpleInGrammar simple_srts fn es (GrammarDef sv grl) =
    GrammarDef (filter (not . simpleGrammarDecls simple_srts) sv)
        . filter (not . simpleProdGRL simple_srts) $ map (adjustSimpleInGRL fn es) grl

simpleGrammarDecls :: M.HashMap Symbol (Symbol, [SortedVar]) -> SortedVar -> Bool
simpleGrammarDecls simple_srts (SortedVar _ (IdentSort (ISymb s))) = s `M.member` simple_srts


simpleProdGRL :: M.HashMap Symbol (Symbol, [SortedVar]) -> GroupedRuleList -> Bool
simpleProdGRL simple_srts (GroupedRuleList _ (IdentSort (ISymb s)) _) = s `M.member` simple_srts

adjustSimpleInGRL :: Symbol -> EliminatedSimple -> GroupedRuleList -> GroupedRuleList
adjustSimpleInGRL fn es (GroupedRuleList symb srt gtrm) =
    GroupedRuleList symb srt $ map (adjustSimpleInGTerms fn es) gtrm

adjustSimpleInGTerms :: Symbol -> EliminatedSimple -> GTerm -> GTerm
adjustSimpleInGTerms fn es (GBfTerm (BfIdentifierBfs (ISymb s) _))
    | Just v <- selectorToVar fn s es = GBfTerm $ BfIdentifier (ISymb v)
adjustSimpleInGTerms _ _ gt = gt

getSimpleSorts :: [Cmd] -> M.HashMap Symbol (Symbol, [SortedVar])
getSimpleSorts =
    M.fromList
    . concatMap (\case
                    SmtCmd (DeclareDatatype s dtdec)
                        | Just dti <- isSimpleDT dtdec -> [(s, dti)]
                    SmtCmd (DeclareDatatypes _ _) -> error "getEliminatedSimple: declareDatatypes not supported"
                    _ -> [])

getSimpleDTs :: M.HashMap Symbol (Symbol, [SortedVar]) -> S.Set Symbol
getSimpleDTs = S.fromList . map fst . M.elems

isSimpleDT :: DTDec -> Maybe (Symbol, [SortedVar])
isSimpleDT (DTDec [DTConsDec dtn sv])
    | all isPrimitiveSV sv = Just (dtn, sv)
isSimpleDT _ = Nothing

isPrimitiveSV :: SortedVar -> Bool
isPrimitiveSV (SortedVar _ (IdentSort (ISymb i))) = i == "Int" || i == "Real" || i == "Bool"
isPrimitiveSV _ = False

-----------------------------------------

-- | Given information about eliminated simple ADTs, restore a solution
restoreSimpleDTs :: EliminatedSimple -> [Cmd] -> [Cmd]
restoreSimpleDTs es = map (restoreSimpleDTs' es)

restoreSimpleDTs' :: EliminatedSimple -> Cmd -> Cmd
restoreSimpleDTs' es (SmtCmd cmd) = SmtCmd $ restoreSimpleDTsSMT es cmd
restoreSimpleDTs' _ _ = error "restoreSimpleDTs: Cmd not supported"

restoreSimpleDTsSMT :: EliminatedSimple -> SmtCmd -> SmtCmd
restoreSimpleDTsSMT es (DefineFun fn sv srt t) =
    let
        sv' = maybe sv id (lookupArgsES fn es)
    in
    DefineFun fn sv' srt $ restoreSimpleDTsTerm es fn t
restoreSimpleDTsSMT _ _ = error "restoreSimpleDTsSMT: Cmd not supported"

restoreSimpleDTsTerm :: EliminatedSimple -> Symbol ->  Term -> Term
restoreSimpleDTsTerm es fn t@(TermIdent i)
    | ISymb s <- i
    , Just t' <- lookupTermES (fn, s) es = t'
    | otherwise = t
restoreSimpleDTsTerm es fn (TermCall i ts) = TermCall i $ map (restoreSimpleDTsTerm es fn) ts
restoreSimpleDTsTerm es fn (TermExists sv t) = TermExists sv $ restoreSimpleDTsTerm es fn t
restoreSimpleDTsTerm es fn (TermForAll sv t) = TermForAll sv $ restoreSimpleDTsTerm es fn t
restoreSimpleDTsTerm _ _ (TermLet _ _ ) = error "restoreSimpleDTsTerm: Term not supported"
restoreSimpleDTsTerm _ _ t = t

-----------------------------------------