{-# LANGUAGE LambdaCase #-}

module G2.Liquid.Inference.Sygus.SimplifySygus ( EliminatedSimple
                                               , elimSimpleDTs
                                               , restoreSimpleDTs 

                                               , elimRedundantAnds
                                               , splitAnds
                                               , simplifyImpliesLHS
                                               , simplifyNegatedAnds

                                               , EliminatedTrivTrue
                                               , simplifyToTrue
                                               , restoreSimplifiedToTrue

                                               , elimNegatedExistential
                                               , simplifyImpliesExistentials) where

import Sygus.Syntax

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
    mapAccumL (elimSimpleDTs' simple_srts) emptyES
        $ filter (not . droppableDTDecl simple_srts) cmds

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
    , Just (_, params) <- M.lookup isrt simple_srts =
        let
            new_sv = map (\(SortedVar n i) -> SortedVar (symb ++ "__" ++ n) i) params
            es' = foldr (\(SortedVar n _) -> insertTermES (fn, symb ++ "__" ++ n) (TermCall (ISymb n) [TermIdent (ISymb symb)])) es params
        in
        (es', new_sv)
    | otherwise = (es, [sv])

elimSimpleDTsTerms :: M.HashMap Symbol (Symbol, [SortedVar]) -> Term -> Term
elimSimpleDTsTerms _ t@(TermIdent _) = t
elimSimpleDTsTerms _ t@(TermLit _) = t
elimSimpleDTsTerms simple_srts (TermCall i ts) =
    swapToIdent . TermCall i $ concatMap (elimSimpleDTsList simple_srts) ts
elimSimpleDTsTerms simple_srts (TermExists sv t) =
    let
        (es, out_as) = mapAccumL
                            (\els (SortedVar n srt) ->
                                            case M.lookup (sortSymb srt) simple_srts of
                                                Just (_, as) ->
                                                    let
                                                        new_as = map (\(SortedVar s srt') -> SortedVar ("new__" ++ s) srt') as
                                                        els' = insertArgsES n new_as els
                                                    in
                                                    (els', new_as)
                                                Nothing -> (els, [SortedVar n srt])) emptyES sv
    in
    case concat out_as of
        [] -> elimExistentials es t'
        out_as' -> TermExists out_as' $ elimExistentials es t'
    where
        t' = elimSimpleDTsTerms simple_srts t
elimSimpleDTsTerms _ t = error $ "elimSimpleDTsTerms: Unhandled term " ++ show t

sortSymb :: Sort -> Symbol
sortSymb (IdentSort (ISymb symb)) = symb
sortSymb (IdentSortSort (ISymb symb) _) = symb

elimSimpleDTsList :: M.HashMap Symbol (Symbol, [SortedVar]) -> Term -> [Term]
elimSimpleDTsList simple_srts t@(TermIdent (ISymb s))
    | s `S.member` getSimpleDTs simple_srts = []
    | otherwise = [t]
elimSimpleDTsList _ t@(TermLit _) = [t]
elimSimpleDTsList simple_srts (TermCall (ISymb s) ts)
    | s `S.member` getSimpleDTs simple_srts = ts
    | otherwise = [swapToIdent . TermCall (ISymb s) $ concatMap (elimSimpleDTsList simple_srts) ts]
elimSimpleDTsList simple_srts te@(TermExists _ _) = [elimSimpleDTsTerms simple_srts te]
elimSimpleDTsList _ t = error $ "elimSimpleDTsList: Unhandled term " ++ show t

elimExistentials :: EliminatedSimple -> Term -> Term
elimExistentials _ t@(TermIdent _) = t
elimExistentials _ t@(TermLit _) = t
elimExistentials es (TermCall i ts) =
    swapToIdent . TermCall i $ concatMap (elimExistentialsList es) ts
elimExistentials _ t = error $ "elimExistentials: Unhandled term " ++ show t

elimExistentialsList :: EliminatedSimple -> Term -> [Term]
elimExistentialsList es t@(TermIdent (ISymb s)) =
    case lookupArgsES s es of
        Just as -> map (\(SortedVar i _) -> TermIdent $ ISymb i) as
        Nothing -> [t]
elimExistentialsList _ t@(TermLit _) = [t]
elimExistentialsList es (TermCall i@(ISymb s) ts)
    | Just _ <- lookupArgsES s es = ts
    | otherwise = [swapToIdent . TermCall i $ map (elimExistentials es) ts]
elimExistentialsList _ t = error $ "elimExistentialsList: Unhandled term " ++ show t

swapToIdent :: Term -> Term
swapToIdent (TermCall i []) = TermIdent i
swapToIdent t = t

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


-----------------------------------------
droppableDTDecl :: M.HashMap Symbol (Symbol, [SortedVar]) -> Cmd -> Bool
droppableDTDecl simple_srts (SmtCmd (DeclareDatatype symb _)) = symb `M.member` simple_srts
droppableDTDecl _ _ = False

-----------------------------------------

-- Maps Sorts with single data constructors to
--  (1) the data constructor name
--  (2) the data constructor arguments.
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
-- Rewrites to remove redundant Ands

elimRedundantAnds :: [Cmd] -> [Cmd]
elimRedundantAnds = map elimRedundantAnds'

elimRedundantAnds' :: Cmd -> Cmd
elimRedundantAnds' (Constraint t) = Constraint $ elimRedAndsTerm t
elimRedundantAnds' cmd = cmd

elimRedAndsTerm :: Term -> Term
elimRedAndsTerm (TermCall (ISymb "and") ts) =
    TermCall (ISymb "and") $ concatMap inlineAnds ts
elimRedAndsTerm t = t

inlineAnds :: Term -> [Term]
inlineAnds (TermCall (ISymb "and") ts) = concatMap inlineAnds ts
inlineAnds t = [t]

-----------------------------------------
-- Split up anded terms into separate constraints

splitAnds :: [Cmd] -> [Cmd]
splitAnds = concatMap splitAnds'

splitAnds' :: Cmd -> [Cmd]
splitAnds' (Constraint t) = splitAndsTerm t
splitAnds' cmd = [cmd]

splitAndsTerm :: Term -> [Cmd]
splitAndsTerm (TermCall (ISymb "and") ts) = map Constraint ts
splitAndsTerm t = [Constraint t]

-----------------------------------------
-- Simplify by eliminatng any functions from the LHS of an implies that must be true

simplifyImpliesLHS :: [Cmd] -> [Cmd]
simplifyImpliesLHS cmd =
    let
        true_trms = mapMaybe getTrueTerm cmd
    in
    map (simplifyImpliesLHS' true_trms) cmd

simplifyImpliesLHS' :: [Term] -> Cmd -> Cmd
simplifyImpliesLHS' ts (Constraint t) = Constraint $ simplifyImpliesLHSTerm ts t
simplifyImpliesLHS' _ cmd = cmd

simplifyImpliesLHSTerm :: [Term] -> Term -> Term
simplifyImpliesLHSTerm ts (TermCall (ISymb "=>") [lhs, rhs]) =
    case simplifyImpliesLHSTerm' ts lhs of
        Just lhs' -> TermCall (ISymb "=>") [lhs', rhs]
        Nothing -> rhs
simplifyImpliesLHSTerm _ t = t

simplifyImpliesLHSTerm' :: [Term] -> Term -> Maybe Term
simplifyImpliesLHSTerm' ts (TermCall (ISymb "and") and_ts) =
    case mapMaybe (simplifyImpliesLHSTerm' ts) and_ts of
        [] -> Just . TermLit $ LitBool True
        and_ts' -> Just $ TermCall (ISymb "and") and_ts'
simplifyImpliesLHSTerm' ts t = if t `elem` ts then Nothing else Just t

getTrueTerm :: Cmd -> Maybe Term
getTrueTerm (Constraint t) = Just t
getTrueTerm _ = Nothing

-----------------------------------------
-- Simplify by eliminatng any functions from a not-ed and that must be true

simplifyNegatedAnds :: [Cmd] -> [Cmd]
simplifyNegatedAnds cmd =
    let
        true_trms = mapMaybe getTrueTerm cmd
    in
    map (simplifyNegatedAnds' true_trms) cmd

simplifyNegatedAnds' :: [Term] -> Cmd -> Cmd
simplifyNegatedAnds' ts (Constraint t) = Constraint $ simplifyNegatedAndsTerms ts t
simplifyNegatedAnds' _ cmd = cmd

simplifyNegatedAndsTerms :: [Term] -> Term -> Term
simplifyNegatedAndsTerms ts (TermCall (ISymb "not") [t]) =
    TermCall (ISymb "not") $ [simplifyNegatedAndsInNot ts t]
simplifyNegatedAndsTerms ts tc@(TermCall (ISymb "=>") [t, t'])
    | t == TermLit (LitBool True) = simplifyNegatedAndsTerms ts t'
    | otherwise = tc
simplifyNegatedAndsTerms _ t = t

simplifyNegatedAndsInNot :: [Term] -> Term -> Term
simplifyNegatedAndsInNot ts (TermCall (ISymb "and") ts') =
    case filter (`notElem` ts) ts' of
        [] -> TermLit (LitBool True)
        new_ts -> TermCall (ISymb "and") new_ts
simplifyNegatedAndsInNot _ t = t

-----------------------------------------
-- Identify functions that can simply be rewritten to true, use `restoreSimplifiedToTrue`
-- to ensure all functions still appear in the returned solution

newtype EliminatedTrivTrue = EliminatedTrivTrue [Cmd]

simplifyToTrue :: [Cmd] -> (EliminatedTrivTrue, [Cmd])
simplifyToTrue cmds =
    let
        synth_funs = mapMaybe getSynthFuns cmds
        may_need_false = concatMap mayNeedToBeFalse cmds

        synth_set_true = filter (\(n, _, _) -> n `notElem` may_need_false) synth_funs
        synth_set_true' = map (\(n, _, _) -> n) synth_set_true

        -- Set up EliminatedTrivTrue
        tre = TermLit (LitBool True)
        triv_def = map (\(n, ar, r) -> SmtCmd $ DefineFun n ar r tre) synth_set_true
    in
    (EliminatedTrivTrue triv_def, filter (not . mustBeTrue synth_set_true') cmds)

getSynthFuns :: Cmd -> Maybe (Symbol, [SortedVar], Sort)
getSynthFuns (SynthFun n ars ret _) = Just (n, ars, ret)
getSynthFuns _ = Nothing

mayNeedToBeFalse :: Cmd -> [Symbol]
mayNeedToBeFalse (Constraint t) = mayNeedToBeFalseTerm t
mayNeedToBeFalse _ = []

mustBeTrue :: [Symbol] -> Cmd -> Bool
mustBeTrue symbs (SynthFun n _ _ _) = n `elem` symbs
mustBeTrue symbs (Constraint (TermIdent (ISymb s))) = s `elem` symbs
mustBeTrue symbs (Constraint (TermCall (ISymb s) _)) = s `elem` symbs
mustBeTrue _ _ = False

-- If a function is called directly in a constraint, it must be true, but if
-- it is nested in an implies or a not, it may need to be false
mayNeedToBeFalseTerm :: Term -> [Symbol]
mayNeedToBeFalseTerm (TermIdent _) = []
mayNeedToBeFalseTerm (TermLit _) = []
mayNeedToBeFalseTerm (TermCall _ ts) = concatMap mayNeedToBeFalseTerm' ts
mayNeedToBeFalseTerm (TermExists _ t) = mayNeedToBeFalseTerm' t -- Could this just be (mayNeedToBeFalseTerm t)?
mayNeedToBeFalseTerm _ = error "mayNeedToBeFalseTerm: unhandled term" 

mayNeedToBeFalseTerm' :: Term -> [Symbol]
mayNeedToBeFalseTerm' (TermIdent (ISymb s)) = [s]
mayNeedToBeFalseTerm' (TermLit _) = []
mayNeedToBeFalseTerm' (TermCall (ISymb s) ts) = s:concatMap mayNeedToBeFalseTerm' ts
mayNeedToBeFalseTerm' (TermExists _ t) = mayNeedToBeFalseTerm' t
mayNeedToBeFalseTerm' _ = error "mayNeedToBeFalseTerm': unhandled term" 

restoreSimplifiedToTrue :: EliminatedTrivTrue -> [Cmd] -> [Cmd]
restoreSimplifiedToTrue (EliminatedTrivTrue el_cmds) = (++) el_cmds


-----------------------------------------
-- Elimiantes negated existentials.  This simplification actually does NOT keep exactly the same problem.
-- However, in practice, we never benefit from negated existentials when synthesizing a refinement type.

elimNegatedExistential :: [Cmd] -> [Cmd]
elimNegatedExistential = map elimNegatedExistential'

elimNegatedExistential' :: Cmd -> Cmd
elimNegatedExistential' (Constraint t) = Constraint $ elimNegatedExistentialTerm t
elimNegatedExistential' cmd = cmd

elimNegatedExistentialTerm :: Term -> Term
elimNegatedExistentialTerm (TermCall (ISymb "not") [t]) =
    case elimNegatedExistentialTerm' t of
        Nothing -> TermLit (LitBool True)
        Just t' -> TermCall (ISymb "not") [t']
elimNegatedExistentialTerm (TermCall i ts) = TermCall i $ map elimNegatedExistentialTerm ts
elimNegatedExistentialTerm t = t

elimNegatedExistentialTerm' :: Term -> Maybe Term
elimNegatedExistentialTerm' (TermExists _ _) = Nothing
elimNegatedExistentialTerm' (TermCall (ISymb "and") ts) = 
    case mapMaybe elimNegatedExistentialTerm' ts of
        [] -> Just $ TermLit (LitBool True)
        ts' -> Just $ TermCall (ISymb "and") ts'
elimNegatedExistentialTerm' t = Just t

-----------------------------------------
-- Simplify by eliminatng any existentials from an implies that must be true.
-- This simplification actually does NOT keep exactly the same problem.
-- However, in practice, we never benefit from negated existentials on the LHS of an implies.

simplifyImpliesExistentials :: [Cmd] -> [Cmd]
simplifyImpliesExistentials cmd =
    map simplifyImpliesExistentials' cmd

simplifyImpliesExistentials' :: Cmd -> Cmd
simplifyImpliesExistentials' (Constraint t) = Constraint $ simplifyImpliesExistentialsTerm t
simplifyImpliesExistentials' cmd = cmd

simplifyImpliesExistentialsTerm :: Term -> Term
simplifyImpliesExistentialsTerm (TermCall (ISymb "=>") [lhs, rhs]) =
    TermCall (ISymb "=>") [simplifyImpliesExistentialsTerm' lhs, rhs]
simplifyImpliesExistentialsTerm t = t

simplifyImpliesExistentialsTerm' :: Term -> Term
simplifyImpliesExistentialsTerm' (TermCall (ISymb "and") and_ts) =
    case map simplifyImpliesExistentialsTerm' and_ts of
        [] ->  TermLit $ LitBool True
        and_ts' -> TermCall (ISymb "and") and_ts'
simplifyImpliesExistentialsTerm' (TermExists _ _) = TermLit $ LitBool True
simplifyImpliesExistentialsTerm' t = t
