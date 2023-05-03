{-# LANGUAGE OverloadedStrings #-}

module G2.Lib.Printers ( PrettyGuide
                       , mkPrettyGuide
                       , updatePrettyGuide

                       , printName

                       , printHaskell
                       , printHaskellDirty
                       , printHaskellDirtyPG
                       , printHaskellPG
                       , mkUnsugaredExprHaskell
                       , mkTypeHaskell
                       , mkTypeHaskellPG
                       , pprExecStateStr
                       , printFuncCall
                       , prettyState

                       , prettyGuideStr) where

import G2.Language.Expr
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues
import G2.Language.Naming
import qualified G2.Language.PathConds as PC
import G2.Language.TypeClasses
import G2.Language.Typing
import G2.Language.Stack
import G2.Language.Syntax
import G2.Language.Support

import Data.Char
import Data.List as L
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.Text as T

data Clean = Cleaned | Dirty deriving Eq

mkIdHaskell :: PrettyGuide -> Id -> String
mkIdHaskell pg (Id n _) = mkNameHaskell pg n

printName :: PrettyGuide -> Name -> String
printName = mkNameHaskell

mkNameHaskell :: PrettyGuide -> Name -> String
mkNameHaskell pg n
    | Just s <- lookupPG n pg = s
    | otherwise = T.unpack (nameOcc n)

mkUnsugaredExprHaskell :: State t -> Expr -> String
mkUnsugaredExprHaskell (State {known_values = kv, type_classes = tc}) =
    mkExprHaskell Cleaned (mkPrettyGuide ()) . modifyMaybe (mkCleanExprHaskell' kv tc)

printHaskell :: State t -> Expr -> String
printHaskell = mkCleanExprHaskell (mkPrettyGuide ())

printHaskellDirty :: Expr -> String
printHaskellDirty = mkExprHaskell Dirty (mkPrettyGuide ())

printHaskellDirtyPG :: PrettyGuide -> Expr -> String
printHaskellDirtyPG = mkExprHaskell Dirty

printHaskellPG :: PrettyGuide -> State t -> Expr -> String
printHaskellPG = mkCleanExprHaskell

mkCleanExprHaskell :: PrettyGuide -> State t -> Expr -> String
mkCleanExprHaskell pg (State {known_values = kv, type_classes = tc}) = 
    mkExprHaskell Cleaned pg . modifyMaybe (mkCleanExprHaskell' kv tc)

mkCleanExprHaskell' :: KnownValues -> TypeClasses -> Expr -> Maybe Expr
mkCleanExprHaskell' kv tc e
    | (App (Data (DataCon n _)) e') <- e
    , n == dcInt kv || n == dcFloat kv || n == dcDouble kv || n == dcInteger kv || n == dcChar kv = Just e'

    | Case scrut i t [a] <- e = Case scrut i t . (:[]) <$> elimPrimDC a

    | (App e' e'') <- e
    , t <- typeOf e'
    , isTypeClass tc t = Just e''

    | (App e' e'') <- e
    , t <- typeOf e''
    , isTypeClass tc t = Just e'

    | (App e' e'') <- e
    , isTypeClass tc (returnType e'') = Just e'

    | App e' (Type _) <- e = Just e'

    | otherwise = Nothing

elimPrimDC :: Alt -> Maybe Alt
elimPrimDC (Alt (DataAlt (DataCon (Name n _ _ _) t) is) e)
    | n == "I#" || n == "F#" || n == "D#" || n == "Z#" || n == "C#" =
                        Just $ Alt (DataAlt (DataCon (Name "" Nothing 0 Nothing) t) is) e
elimPrimDC _ = Nothing

mkDirtyExprHaskell :: PrettyGuide -> Expr -> String
mkDirtyExprHaskell = mkExprHaskell Dirty

mkExprHaskell :: Clean -> PrettyGuide -> Expr -> String
mkExprHaskell = mkExprHaskell' 0

mkExprHaskell' :: Int -> Clean -> PrettyGuide -> Expr -> String
mkExprHaskell' off_init cleaned pg ex = mkExprHaskell'' off_init ex
    where
        isCleaned = cleaned == Cleaned

        mkExprHaskell'' :: Int -- ^ How much should a new line be indented?
                       -> Expr
                       -> String
        mkExprHaskell'' _ (Var ids) = mkIdHaskell pg ids
        mkExprHaskell'' _ (Lit c) = mkLitHaskell c
        mkExprHaskell'' _ (Prim p _) = mkPrimHaskell p
        mkExprHaskell'' off (Lam _ ids e) =
            "(\\" ++ mkIdHaskell pg ids ++ " -> " ++ mkExprHaskell'' off e ++ ")"

        mkExprHaskell'' off a@(App ea@(App e1 e2) e3)
            | Data (DataCon n _) <- appCenter a
            , isTuple n
            , isCleaned = printTuple pg a
            | Data (DataCon n _) <- appCenter a
            , isPrimTuple n
            , isCleaned = printPrimTuple pg a

            | Data (DataCon n1 _) <- e1
            , nameOcc n1 == ":"
            , isCleaned =
                if isLitChar e2 then printString pg a else printList pg a

            | isInfixable e1
            , isCleaned =
                let
                    e2P = if isApp e2 then "(" ++ mkExprHaskell'' off e2 ++ ")" else mkExprHaskell'' off e2
                    e3P = if isApp e3 then "(" ++ mkExprHaskell'' off e3 ++ ")" else mkExprHaskell'' off e3
                in
                e2P ++ " " ++ mkExprHaskell'' off e1 ++ " " ++ e3P

            | App _ _ <- e3 = mkExprHaskell'' off ea ++ " (" ++ mkExprHaskell'' off e3 ++ ")"
            | otherwise = mkExprHaskell'' off ea ++ " " ++ mkExprHaskell'' off e3

        mkExprHaskell'' off (App e1 ea@(App _ _)) = mkExprHaskell'' off e1 ++ " (" ++ mkExprHaskell'' off ea ++ ")"
        mkExprHaskell'' off (App e1 e2) =
            parenWrap e1 (mkExprHaskell'' off e1) ++ " " ++ mkExprHaskell'' off e2
        mkExprHaskell'' _ (Data d) = mkDataConHaskell pg d
        mkExprHaskell'' off (Case e bndr _ ae) =
               "case " ++ parenWrap e (mkExprHaskell'' off e) ++ " of\n" 
            ++ intercalate "\n" (map (mkAltHaskell (off + 2) cleaned pg bndr) ae)
        mkExprHaskell'' _ (Type t) = "@" ++ mkTypeHaskellPG pg t
        mkExprHaskell'' off (Cast e (t1 :~ t2)) =
            let
                e_str = mkExprHaskell'' off e
                t1_str = mkTypeHaskellPG pg t1
                t2_str = mkTypeHaskellPG pg t2
            in
            "((coerce (" ++ e_str ++ " :: " ++ t1_str ++ ")) :: " ++ t2_str ++ ")"
        mkExprHaskell'' off (Let binds e) =
            let
                binds' = intercalate (offset off ++ "\n")
                       $ map (\(i, be) -> mkIdHaskell pg i ++ " = " ++ mkExprHaskell'' off be) binds 
            in
            "let " ++ binds' ++ " in " ++ mkExprHaskell'' off e
        mkExprHaskell'' off (Tick nl e) = "TICK[" ++ printTickish pg nl ++ "]{" ++ mkExprHaskell'' off e ++ "}"
        mkExprHaskell'' off (Assume m_fc e1 e2) =
            let
                print_fc = maybe "" (\fc -> "(" ++ printFuncCallPG pg fc ++ ") ") m_fc
            in
            "assume " ++ print_fc
                ++ "(" ++ mkExprHaskell'' off e1
                ++ ") (" ++ mkExprHaskell'' off e2 ++ ")"
        mkExprHaskell'' off (Assert m_fc e1 e2) =
            let
                print_fc = maybe "" (\fc -> "(" ++ printFuncCallPG pg fc ++ ") ") m_fc
            in
            "assert " ++ print_fc
                ++ "(" ++ mkExprHaskell'' off e1
                ++ ") (" ++ mkExprHaskell'' off e2 ++ ")"
        mkExprHaskell'' off (NonDet es) =
            let
                print_es = map (mkExprHaskell'' off) es
            in
            intercalate ("\n" ++ offset off ++ "[NonDet]\n") print_es 
        mkExprHaskell'' _ (SymGen t) = "(symgen " ++ mkTypeHaskellPG pg t ++ ")"
        mkExprHaskell'' _ e = "e = " ++ show e ++ " NOT SUPPORTED"

        parenWrap :: Expr -> String -> String
        parenWrap (Case _ _ _ _) s = "(" ++ s ++ ")"
        parenWrap (Let _ _) s = "(" ++ s ++ ")"
        parenWrap (Tick _ e) s = parenWrap e s
        parenWrap _ s = s

mkAltHaskell :: Int -> Clean -> PrettyGuide -> Id -> Alt -> String
mkAltHaskell off cleaned pg i_bndr@(Id bndr_name _) (Alt am e) =
    let
        needs_bndr = bndr_name `elem` names e
    in
    offset off ++ mkAltMatchHaskell (if needs_bndr then Just i_bndr else Nothing) am ++ " -> " ++ mkExprHaskell' off cleaned pg e
    where
        mkAltMatchHaskell :: Maybe Id -> AltMatch -> String
        mkAltMatchHaskell m_bndr (DataAlt dc@(DataCon n _) ids) | isTuple n =
            let
                pr_am = printTuple pg $ mkApp (Data dc:map Var ids)
            in
            case m_bndr of
                Just bndr | not (L.null ids) -> mkIdHaskell pg bndr ++ "@" ++ pr_am ++ ""
                          | otherwise -> mkIdHaskell pg bndr
                Nothing -> pr_am
        mkAltMatchHaskell m_bndr (DataAlt dc@(DataCon n _) [id1, id2]) | isInfixableName n =
            let
                pr_am = mkIdHaskell pg id1 ++ " " ++ mkDataConHaskell pg dc ++ " " ++ mkIdHaskell pg id2
            in
            case m_bndr of
                Just bndr -> mkIdHaskell pg bndr ++ "@(" ++ pr_am ++ ")" 
                Nothing -> pr_am
        mkAltMatchHaskell m_bndr (DataAlt dc ids) =
            let
                pr_am = mkDataConHaskell pg dc ++ " " ++ intercalate " "  (map (mkIdHaskell pg) ids)
            in
            case m_bndr of
                Just bndr | not (L.null ids) -> mkIdHaskell pg bndr ++ "@(" ++ pr_am ++ ")"
                          | otherwise -> mkIdHaskell pg bndr
                Nothing -> pr_am
        mkAltMatchHaskell m_bndr (LitAlt l) =
            case m_bndr of
                Just bndr -> mkIdHaskell pg bndr ++ "@" ++ mkLitHaskell l
                Nothing -> mkLitHaskell l
        mkAltMatchHaskell (Just bndr) Default = mkIdHaskell pg bndr
        mkAltMatchHaskell _ Default = "_"

mkDataConHaskell :: PrettyGuide -> DataCon -> String
-- Special casing for Data.Map in the modified base
mkDataConHaskell _ (DataCon (Name "Assocs" _ _ _) _) = "fromList"
mkDataConHaskell pg (DataCon n _) = mkNameHaskell pg n

offset :: Int -> String
offset i = duplicate "   " i

printList :: PrettyGuide -> Expr -> String
printList pg a =
    let (strs, b) = printList' pg a
    in case b of
        False -> "(" ++ intercalate ":" strs ++ ")"
        _ -> "[" ++ intercalate ", " strs ++ "]"

printList' :: PrettyGuide -> Expr -> ([String], Bool)
printList' pg (App (App e1 e) e') | Data (DataCon n1 _) <- e1
                                  , nameOcc n1 == ":" =
    let (strs, b) = printList' pg e'
    in (mkExprHaskell Cleaned pg e:strs, b)
printList' pg e | Data (DataCon n _) <- appCenter e
                , nameOcc n == "[]" = ([], True)
                | otherwise = ([mkExprHaskell Cleaned pg e], False)

printString :: PrettyGuide -> Expr -> String
printString pg a =
    let
        maybe_str = printString' a
    in case maybe_str of
        Just str -> if all isPrint str then "\"" ++ str ++ "\""
                    else "[" ++ intercalate ", " (map stringToEnum str) ++ "]"
        Nothing -> printList pg a
    where
        stringToEnum c
            | isPrint c = '\'':c:'\'':[]
            | otherwise = "toEnum " ++ show (ord c)

printString' :: Expr -> Maybe String
printString' (App (App _ (Lit (LitChar c))) e') =
    case printString' e' of
        Nothing -> Nothing
        Just str -> Just (c:str)
printString' e | Data (DataCon n _) <- appCenter e
               , nameOcc n == "[]" = Just []
               | otherwise = Nothing

isTuple :: Name -> Bool
isTuple (Name n _ _ _) = fmap fst (T.uncons n) == Just '(' && fmap snd (T.unsnoc n) == Just ')'
                     && T.all (\c -> c == '(' || c == ')' || c == ',') n

isPrimTuple :: Name -> Bool
isPrimTuple (Name n _ _ _) = fmap fst (T.uncons n) == Just '(' && fmap snd (T.unsnoc n) == Just ')'
                     && T.all (\c -> c == '(' || c == ')' || c == ',' || c == '#') n
                     && T.any (\c -> c == '#') n

printTuple :: PrettyGuide -> Expr -> String
printTuple pg a = "(" ++ intercalate ", " (reverse $ printTuple' pg a) ++ ")"

printPrimTuple :: PrettyGuide -> Expr -> String
printPrimTuple pg a = "(#" ++ intercalate ", " (reverse $ printTuple' pg a) ++ "#)"

printTuple' :: PrettyGuide -> Expr -> [String]
printTuple' pg (App e e') = mkExprHaskell Cleaned pg e':printTuple' pg e
printTuple' _ _ = []


isInfixable :: Expr -> Bool
isInfixable (Var (Id n _)) = isInfixableName n
isInfixable (Data (DataCon n _)) = isInfixableName n
isInfixable (Prim p _) = not . any isAlphaNum $ mkPrimHaskell p
isInfixable _ = False

isInfixableName :: Name -> Bool
isInfixableName = not . T.any isAlphaNum . nameOcc

isApp :: Expr -> Bool
isApp (App _ _) = True
isApp _ = False

isLitChar :: Expr -> Bool
isLitChar (Lit (LitChar _)) = True
isLitChar _ = False

mkLitHaskell :: Lit -> String
mkLitHaskell (LitInt i) = if i < 0 then "(" ++ show i ++ ")" else show i
mkLitHaskell (LitInteger i) = if i < 0 then "(" ++ show i ++ ")" else show i
mkLitHaskell (LitFloat r) = "(" ++ show ((fromRational r) :: Float) ++ ")"
mkLitHaskell (LitDouble r) = "(" ++ show ((fromRational r) :: Double) ++ ")"
mkLitHaskell (LitChar c) = ['\'', c, '\'']
mkLitHaskell (LitString s) = s

mkPrimHaskell :: Primitive -> String
mkPrimHaskell Ge = ">="
mkPrimHaskell Gt = ">"
mkPrimHaskell Eq = "=="
mkPrimHaskell Neq = "/="
mkPrimHaskell Lt = "<"
mkPrimHaskell Le = "<="
mkPrimHaskell And = "&&"
mkPrimHaskell Or = "||"
mkPrimHaskell Not = "not"
mkPrimHaskell Plus = "+"
mkPrimHaskell Minus = "-"
mkPrimHaskell Mult = "*"
mkPrimHaskell Div = "/"
mkPrimHaskell DivInt = "/"
mkPrimHaskell Quot = "quot"
mkPrimHaskell Mod = "mod"
mkPrimHaskell Rem = "rem"
mkPrimHaskell Negate = "-"
mkPrimHaskell Abs = "abs"
mkPrimHaskell SqRt = "sqrt"

mkPrimHaskell DataToTag = "prim_dataToTag#"
mkPrimHaskell TagToEnum = "prim_tagToEnum#"


mkPrimHaskell IntToFloat = "fromIntegral"
mkPrimHaskell IntToDouble = "fromIntegral"
mkPrimHaskell RationalToDouble = "fromRational"
mkPrimHaskell FromInteger = "fromInteger"
mkPrimHaskell ToInteger = "toInteger"

mkPrimHaskell Chr = "chr"
mkPrimHaskell OrdChar = "ord"

mkPrimHaskell ToInt = "toInt"

mkPrimHaskell Error = "error"
mkPrimHaskell Undefined = "undefined"
mkPrimHaskell Implies = "undefined"
mkPrimHaskell Iff = "undefined"

mkTypeHaskell :: Type -> String
mkTypeHaskell = mkTypeHaskellPG (mkPrettyGuide ())

mkTypeHaskellPG :: PrettyGuide -> Type -> String
mkTypeHaskellPG pg (TyVar i) = mkIdHaskell pg i
mkTypeHaskellPG pg (TyFun t1 t2) = mkTypeHaskellPG pg t1 ++ " -> " ++ mkTypeHaskellPG pg t2
mkTypeHaskellPG pg (TyCon n _) | nameOcc n == "List"
                               , nameModule n == Just "GHC.Types" = "[]"
                               | otherwise = mkNameHaskell pg n
mkTypeHaskellPG pg (TyApp t1 t2) = "(" ++ mkTypeHaskellPG pg t1 ++ " " ++ mkTypeHaskellPG pg t2 ++ ")"
mkTypeHaskellPG pg (TyForAll i t) = "forall " ++ mkIdHaskell pg i ++ " . " ++ mkTypeHaskellPG pg t
mkTypeHaskellPG _ TYPE = "Type"
mkTypeHaskellPG _ t = "Unsupported type in printer. " ++ show t

duplicate :: String -> Int -> String
duplicate _ 0 = ""
duplicate s n = s ++ duplicate s (n - 1)

printTickish :: PrettyGuide -> Tickish -> String
printTickish _ (Breakpoint sp) = printLoc (start sp) ++ " - " ++ printLoc (end sp)
printTickish pg (NamedLoc n) = mkNameHaskell pg n

printLoc :: Loc -> String
printLoc (Loc ln cl fl) = "(line " ++ show ln ++ " column " ++ show cl ++ " in " ++  fl ++ ")" 

-------------------------------------------------------------------------------

prettyState :: Show t => PrettyGuide -> State t -> String
prettyState pg s =
    injNewLine
        [ ">>>>> [State] >>>>>>>>>>>>>>>>>>>>>"
        , "----- [Code] ----------------------"
        , pretty_curr_expr
        , "----- [Stack] ----------------------"
        , pretty_stack
        , "----- [Env] -----------------------"
        , pretty_eenv
        , "----- [Paths] -----------------------"
        , pretty_paths
        , "----- [Non Red Paths] ---------------------"
        , pretty_non_red_paths
        , "----- [True Assert] ---------------------"
        , show (true_assert s)
        , "----- [Assert FC] ---------------------"
        , pretty_assert_fcs
        , "----- [Tracker] ---------------------"
        , show (track s)
        , "----- [Pretty] ---------------------"
        , pretty_names
        ]
    where
        pretty_curr_expr = prettyCurrExpr pg (curr_expr s)
        pretty_stack = prettyStack pg (exec_stack s)
        pretty_eenv = prettyEEnv pg (expr_env s)
        pretty_paths = prettyPathConds pg (path_conds s)
        pretty_non_red_paths = prettyNonRedPaths pg (non_red_path_conds s)
        pretty_assert_fcs = maybe "None" (printFuncCallPG pg) (assert_ids s)
        pretty_names = prettyGuideStr pg


prettyCurrExpr :: PrettyGuide -> CurrExpr -> String
prettyCurrExpr pg (CurrExpr er e) =
    let
        e_str = mkDirtyExprHaskell pg e
    in
    case er of
        Evaluate -> "evaluate: " ++ e_str
        Return -> "return: " ++ e_str

prettyStack :: PrettyGuide -> Stack Frame -> String
prettyStack pg = intercalate "\n" . map (prettyFrame pg) . toList

prettyFrame :: PrettyGuide -> Frame -> String
prettyFrame pg (CaseFrame i _ as) =
    "case frame: bindee:" ++ mkIdHaskell pg i ++ "\n" ++ intercalate "\n" (map (mkAltHaskell 1 Dirty pg i) as)
prettyFrame pg (ApplyFrame e) = "apply frame: " ++ mkDirtyExprHaskell pg e
prettyFrame pg (UpdateFrame n) = "update frame: " ++ mkNameHaskell pg n
prettyFrame pg (CastFrame (t1 :~ t2)) = "cast frame: " ++ mkTypeHaskellPG pg t1 ++ " ~ " ++ mkTypeHaskellPG pg t2
prettyFrame pg (CurrExprFrame act ce) = "curr_expr frame: " ++ prettyCEAction pg act ++ " " ++ prettyCurrExpr pg ce
prettyFrame pg (AssumeFrame e) = "assume frame: " ++ mkDirtyExprHaskell pg e
prettyFrame pg (AssertFrame m_fc e) =
    let
        fc = case m_fc of
                  Just fc_ -> "(from call " ++ printFuncCallPG pg fc_ ++ ")"
                  Nothing -> ""
    in
    "assert frame: " ++ fc ++ mkDirtyExprHaskell pg e

prettyCEAction :: PrettyGuide -> CEAction -> String
prettyCEAction pg (EnsureEq e) = "EnsureEq " ++ mkDirtyExprHaskell pg e
prettyCEAction _ NoAction = "NoAction"

prettyEEnv :: PrettyGuide -> ExprEnv -> String
prettyEEnv pg =
  intercalate "\n\n" . map (\(n, e) -> mkNameHaskell pg n ++ " = " ++ printEnvObj pg e ) . E.toList

printEnvObj :: PrettyGuide -> E.EnvObj -> String
printEnvObj pg (E.ExprObj e) = mkDirtyExprHaskell pg e
printEnvObj pg (E.SymbObj (Id _ t)) = "symbolic " ++ mkTypeHaskellPG pg t
printEnvObj pg (E.RedirObj n) = "redir to " ++ mkNameHaskell pg n

prettyPathConds :: PrettyGuide -> PathConds -> String
prettyPathConds pg = intercalate "\n" . map (prettyPathCond pg) . PC.toList

prettyPathCond :: PrettyGuide -> PathCond -> String
prettyPathCond pg (AltCond l e b) =
    let
        eq = mkLitHaskell l ++ " = " ++ mkDirtyExprHaskell pg e
    in
    if b then eq else "not (" ++ eq ++ ")"
prettyPathCond pg (ExtCond e b) =
    if b then mkDirtyExprHaskell pg e else "not (" ++ mkDirtyExprHaskell pg e ++ ")"
prettyPathCond pg (SoftPC pc) =
    "soft (" ++ prettyPathCond pg pc ++ ")"
prettyPathCond pg (MinimizePC e) =
    "minimize (" ++ mkDirtyExprHaskell pg e ++ ")"
prettyPathCond pg (AssumePC i l pc) =
    let
        pc' = map PC.unhashedPC $ HS.toList pc
    in
    mkIdHaskell pg i ++ " = " ++ show l ++ "=> (" ++ intercalate "\nand " (map (prettyPathCond pg) pc') ++ ")"

prettyNonRedPaths :: PrettyGuide -> [(Expr, Expr)] -> String
prettyNonRedPaths pg = intercalate "\n" . map (\(e1, e2) -> mkDirtyExprHaskell pg e1 ++ " == " ++ mkDirtyExprHaskell pg e2)

-------------------------------------------------------------------------------

injNewLine :: [String] -> String
injNewLine strs = intercalate "\n" strs

-- | More raw version of state dumps.
pprExecStateStr :: Show t => State t -> Bindings -> String
pprExecStateStr ex_state b = injNewLine acc_strs
  where
    eenv_str = pprExecEEnvStr (expr_env ex_state)
    tenv_str = pprTEnvStr (type_env ex_state)
    estk_str = pprExecStackStr (exec_stack ex_state)
    code_str = pprExecCodeStr (curr_expr ex_state)
    names_str = pprExecNamesStr (name_gen b)
    input_str = pprInputIdsStr (E.symbolicIds . expr_env $ ex_state)
    paths_str = pprPathsStr (PC.toList $ path_conds ex_state)
    non_red_paths_str = injNewLine (map show $ non_red_path_conds ex_state)
    tc_str = pprTCStr (type_classes ex_state)
    walkers_str = show (deepseq_walkers b)
    cleaned_str = pprCleanedNamesStr (cleaned_names b)
    model_str = pprModelStr (model ex_state)
    rules_str = intercalate "\n" $ map show (zip ([0..] :: [Integer]) $ rules ex_state)
    track_str = show (track ex_state)
    acc_strs = [ ">>>>> [State] >>>>>>>>>>>>>>>>>>>>>"
               , "----- [Code] ----------------------"
               , code_str
               , "----- [Stack] ---------------------"
               , estk_str
               , "----- [Env] -----------------------"
               , eenv_str
               , "----- [TEnv] -----------------------"
               , tenv_str
               , "----- [Names] ---------------------"
               , names_str
               , "----- [Input Ids] -----------------"
               , input_str
               , "----- [Walkers] -------------------"
               , walkers_str
               , "----- [Paths] ---------------------"
               , paths_str
               , "----- [Non Red Paths] ---------------------"
               , non_red_paths_str
               , "----- [True Assert] ---------------------"
               , "True Assert = " ++ show (true_assert ex_state)
               , "----- [Assert Ids] ---------------------"
               , show (assert_ids ex_state)
               , "----- [TypeClasses] ---------------------"
               , tc_str
               , "----- [Cleaned] -------------------"
               , cleaned_str
               , "----- [Model] -------------------"
               , model_str
               , "----- [Track] -------------------"
               , track_str
               , "----- [Rules] -------------------"
               , rules_str
               , "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<" 
               ]

pprExecEEnvStr :: E.ExprEnv -> String
pprExecEEnvStr eenv = injNewLine kv_strs
  where
    kv_strs = map (show) $ E.toList eenv

pprTEnvStr :: TypeEnv -> String
pprTEnvStr tenv = injNewLine kv_strs
  where
    kv_strs = map show $ HM.toList tenv

pprModelStr :: Model -> String
pprModelStr m = injNewLine kv_strs
  where
    kv_strs = map show $ HM.toList m

pprExecStackStr :: Stack Frame -> String
pprExecStackStr stk = injNewLine frame_strs
  where
    frame_strs = map pprExecFrameStr $ toList stk

pprExecFrameStr :: Frame -> String
pprExecFrameStr frame = show frame

pprExecCodeStr :: CurrExpr -> String
pprExecCodeStr code = show code

pprExecNamesStr :: NameGen -> String
pprExecNamesStr _ = ""

pprPathsStr :: [PathCond] -> String
pprPathsStr paths = injNewLine cond_strs
  where
    cond_strs = map pprPathCondStr paths

pprTCStr :: TypeClasses -> String
pprTCStr tc = injNewLine cond_strs
  where
    cond_strs = map show $ HM.toList $ toMap tc

pprInputIdsStr :: InputIds -> String
pprInputIdsStr i = injNewLine id_strs
  where
    id_strs = map show i

pprPathCondStr :: PathCond -> String
pprPathCondStr = show

pprCleanedNamesStr :: CleanedNames -> String
pprCleanedNamesStr = injNewLine . map show . HM.toList

printFuncCall :: FuncCall -> String
printFuncCall = printFuncCallPG (mkPrettyGuide ())

printFuncCallPG :: PrettyGuide -> FuncCall -> String
printFuncCallPG pg (FuncCall { funcName = f, arguments = ars, returns = r}) =
    let
        call_str fn = mkDirtyExprHaskell pg . foldl (\a a' -> App a a') (Var (Id fn TyUnknown)) $ ars
        r_str = mkDirtyExprHaskell pg r
    in
    "(" ++ call_str f ++ " " ++ r_str ++ ")"

-------------------------------------------------------------------------------
-- Pretty Guide
-------------------------------------------------------------------------------

-- | Maps G2 `Name`s to printable `String`s uniquely and consistently
-- (two `Name`s will not map to the same `String`, and on a per `PrettyGuide`
-- basis the same `Name` will always map to the same `String`.)
-- The `PrettyGuide` will only work on `Name`s it "knows" about.
-- It "knows" about names in the `Named` value it is passed in it's creation
-- (via `mkPrettyGuide`) and all `Name`s that it is passed via `updatePrettyGuide`.
data PrettyGuide = PG { pg_assigned :: HM.HashMap Name String, pg_nums :: HM.HashMap T.Text Int }

mkPrettyGuide :: Named a => a -> PrettyGuide
mkPrettyGuide = foldr insertPG (PG HM.empty HM.empty) . names

updatePrettyGuide :: Named a => a -> PrettyGuide -> PrettyGuide
updatePrettyGuide ns pg = foldr insertPG pg $ names ns

insertPG :: Name -> PrettyGuide -> PrettyGuide
insertPG n pg@(PG { pg_assigned = as, pg_nums = nms })
    | not (HM.member n as) =
        case HM.lookup (nameOcc n) nms of
            Just i ->
                PG { pg_assigned = HM.insert n (T.unpack (nameOcc n) ++ "'" ++ show i) as
                   , pg_nums = HM.insert (nameOcc n) (i + 1) nms }
            Nothing ->
                PG { pg_assigned = HM.insert n (T.unpack $ nameOcc n) as
                   , pg_nums = HM.insert (nameOcc n) 1 nms }
    | otherwise = pg

lookupPG :: Name -> PrettyGuide -> Maybe String
lookupPG n = HM.lookup n . pg_assigned

prettyGuideStr :: PrettyGuide -> String
prettyGuideStr = intercalate "\n" . map (\(n, s) -> s ++ " <-> " ++ show n) . HM.toList . pg_assigned
