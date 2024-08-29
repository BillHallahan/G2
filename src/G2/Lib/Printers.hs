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
                       , prettyEEnv
                       , prettyTypeEnv 

                       , prettyGuideStr) where

import G2.Language.Expr
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues
import G2.Language.MutVarEnv
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

mkIdHaskell :: PrettyGuide -> Id -> T.Text
mkIdHaskell pg (Id n _) = mkNameHaskell pg n

printName :: PrettyGuide -> Name -> T.Text
printName = mkNameHaskell

mkNameHaskell :: PrettyGuide -> Name -> T.Text
mkNameHaskell pg n
    | Just s <- lookupPG n pg = s
    | otherwise = nameOcc n

mkUnsugaredExprHaskell :: State t -> Expr -> T.Text
mkUnsugaredExprHaskell (State {type_classes = tc}) =
    mkExprHaskell Cleaned (mkPrettyGuide ()) . modifyMaybe (mkCleanExprHaskell' tc)

printHaskell :: State t -> Expr -> T.Text
printHaskell = mkCleanExprHaskell (mkPrettyGuide ())

printHaskellDirty :: Expr -> T.Text
printHaskellDirty = mkExprHaskell Dirty (mkPrettyGuide ())

printHaskellDirtyPG :: PrettyGuide -> Expr -> T.Text
printHaskellDirtyPG = mkExprHaskell Dirty

printHaskellPG :: PrettyGuide -> State t -> Expr -> T.Text
printHaskellPG = mkCleanExprHaskell

mkCleanExprHaskell :: PrettyGuide -> State t -> Expr -> T.Text
mkCleanExprHaskell pg (State {type_classes = tc}) = 
    mkExprHaskell Cleaned pg . modifyMaybe (mkCleanExprHaskell' tc)

mkCleanExprHaskell' :: TypeClasses -> Expr -> Maybe Expr
mkCleanExprHaskell' tc e
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
elimPrimDC (Alt (DataAlt dc@(DataCon (Name n _ _ _) t) is) e)
    | n == "I#" || n == "F#" || n == "D#" || n == "Z#" || n == "C#" =
                        Just $ Alt (DataAlt (DataCon (Name "" Nothing 0 Nothing) t) is) (insertLitDC dc e)
elimPrimDC _ = Nothing

insertLitDC :: DataCon -> Expr -> Expr 
insertLitDC dc (App (App (Prim p t) (Var i)) (Lit l)) = App (App (Prim p t) (Var i)) (App (Data dc) (Lit l)) 
insertLitDC dc e = modifyChildren (insertLitDC dc) e

mkDirtyExprHaskell :: PrettyGuide -> Expr -> T.Text
mkDirtyExprHaskell = mkExprHaskell Dirty

mkExprHaskell :: Clean -> PrettyGuide -> Expr -> T.Text
mkExprHaskell = mkExprHaskell' 0

mkExprHaskell' :: Int -> Clean -> PrettyGuide -> Expr -> T.Text
mkExprHaskell' off_init cleaned pg ex = mkExprHaskell'' off_init ex
    where
        isCleaned = cleaned == Cleaned

        mkExprHaskell'' :: Int -- ^ How much should a new line be indented?
                       -> Expr
                       -> T.Text
        mkExprHaskell'' _ (Var ids) = mkIdHaskell pg ids
        mkExprHaskell'' _ (Lit c) = mkLitHaskell UseHash c
        mkExprHaskell'' _ (Prim p _) = if isCleaned then mkPrimHaskellNoDistFloat pg p else mkPrimHaskell pg p
        mkExprHaskell'' off (Lam _ ids e) =
            "(\\" <> mkIdHaskell pg ids <> " -> " <> mkExprHaskell'' off e <> ")"

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

            | isInfixable pg e1
            , isCleaned =
                let
                    e2P = if isApp e2 then "(" <> mkExprHaskell'' off e2 <> ")" else mkExprHaskell'' off e2
                    e3P = if isApp e3 then "(" <> mkExprHaskell'' off e3 <> ")" else mkExprHaskell'' off e3
                in
                e2P <> " " <> mkExprHaskell'' off e1 <> " " <> e3P

            | App _ _ <- e3 = mkExprHaskell'' off ea <> " (" <> mkExprHaskell'' off e3 <> ")"
            | otherwise = mkExprHaskell'' off ea <> " " <> parenWrap e3 (mkExprHaskell'' off e3)

        mkExprHaskell'' off (App e1 ea@(App _ _)) = parenWrap e1 (mkExprHaskell'' off e1) <> " (" <> mkExprHaskell'' off ea <> ")"
        mkExprHaskell'' _ (App (Data (DataCon (Name n _ _ _) _)) (Lit l)) 
            | n == "I#" || n == "F#" || n == "D#" || n == "Z#" || n == "C#" = mkLitHaskell NoHash l
        mkExprHaskell'' off (App e1 e2) =
            parenWrap e1 (mkExprHaskell'' off e1) <> " " <> parenWrap e2 (mkExprHaskell'' off e2)
        mkExprHaskell'' _ (Data d) = mkDataConHaskell pg d
        mkExprHaskell'' off (Case e bndr _ ae) =
               "case " <> parenWrap e (mkExprHaskell'' off e) <> " of\n" 
            <> T.intercalate "\n" (map (mkAltHaskell (off + 2) cleaned pg bndr) ae)
        mkExprHaskell'' _ (Type t) = "@" <> mkTypeHaskellPG pg t
        mkExprHaskell'' off (Cast e (t1 :~ t2)) =
            let
                e_str = mkExprHaskell'' off e
                t1_str = mkTypeHaskellPG pg t1
                t2_str = mkTypeHaskellPG pg t2
            in
            "((coerce (" <> e_str <> " :: " <> t1_str <> ")) :: " <> t2_str <> ")"
        mkExprHaskell'' _ (Coercion (t1 :~ t2)) =
            let
                t1_str = mkTypeHaskellPG pg t1
                t2_str = mkTypeHaskellPG pg t2
            in
            "(" <> t1_str <> " :~ " <> t2_str <> ")"
        mkExprHaskell'' off (Let binds e) =
            let
                binds' = T.intercalate (offset off <> "\n")
                       $ map (\(i, be) -> mkIdHaskell pg i <> " = " <> mkExprHaskell'' off be) binds 
            in
            "let " <> binds' <> " in " <> mkExprHaskell'' off e
        mkExprHaskell'' off (Tick nl e) = "TICK[" <> printTickish pg nl <> "]{" <> mkExprHaskell'' off e <> "}"
        mkExprHaskell'' off (Assume m_fc e1 e2) =
            let
                print_fc = maybe "" (\fc -> "(" <> printFuncCallPG pg fc <> ") ") m_fc
            in
            "assume " <> print_fc
                <> "(" <> mkExprHaskell'' off e1
                <> ") (" <> mkExprHaskell'' off e2 <> ")"
        mkExprHaskell'' off (Assert m_fc e1 e2) =
            let
                print_fc = maybe "" (\fc -> "(" <> printFuncCallPG pg fc <> ") ") m_fc
            in
            "assert " <> print_fc
                <> "(" <> mkExprHaskell'' off e1
                <> ") (" <> mkExprHaskell'' off e2 <> ")"
        mkExprHaskell'' off (NonDet es) =
            let
                print_es = map (mkExprHaskell'' off) es
            in
            T.intercalate ("\n" <> offset off <> "[NonDet]\n") print_es 
        mkExprHaskell'' _ (SymGen SLog t) = "(symgen log " <> mkTypeHaskellPG pg t <> ")"
        mkExprHaskell'' _ (SymGen SNoLog t) = "(symgen no_log " <> mkTypeHaskellPG pg t <> ")"

        parenWrap :: Expr -> T.Text -> T.Text
        parenWrap (Case _ _ _ _) s = "(" <> s <> ")"
        parenWrap (Let _ _) s = "(" <> s <> ")"
        parenWrap (Tick _ e) s = parenWrap e s
        parenWrap _ s = s

mkAltHaskell :: Int -> Clean -> PrettyGuide -> Id -> Alt -> T.Text
mkAltHaskell off cleaned pg i_bndr@(Id bndr_name _) (Alt am e) =
    let
        needs_bndr = bndr_name `elem` names e
    in
    offset off <> mkAltMatchHaskell (if needs_bndr then Just i_bndr else Nothing) am <> " -> " <> mkExprHaskell' off cleaned pg e
    where
        mkAltMatchHaskell :: Maybe Id -> AltMatch -> T.Text
        mkAltMatchHaskell m_bndr (DataAlt dc@(DataCon n _) ids) | isTuple n =
            let
                pr_am = printTuple pg $ mkApp (Data dc:map Var ids)
            in
            case m_bndr of
                Just bndr | not (L.null ids) -> mkIdHaskell pg bndr <> "@" <> pr_am <> ""
                          | otherwise -> mkIdHaskell pg bndr
                Nothing -> pr_am
        mkAltMatchHaskell m_bndr (DataAlt dc@(DataCon n _) [id1, id2]) | isInfixableName n =
            let
                pr_am = mkIdHaskell pg id1 <> " " <> mkDataConHaskell pg dc <> " " <> mkIdHaskell pg id2
            in
            case m_bndr of
                Just bndr -> mkIdHaskell pg bndr <> "@(" <> pr_am <> ")" 
                Nothing -> pr_am
        mkAltMatchHaskell m_bndr (DataAlt dc ids) =
            let
                pr_am = mkDataConHaskell pg dc <> " " <> T.intercalate " "  (map (mkIdHaskell pg) ids)
            in
            case m_bndr of
                Just bndr -> mkIdHaskell pg bndr <> "@(" <> pr_am <> ")"
                Nothing -> pr_am
        mkAltMatchHaskell m_bndr (LitAlt l) =
            case m_bndr of
                Just bndr -> mkIdHaskell pg bndr <> "@" <> mkLitHaskell NoHash l
                Nothing -> mkLitHaskell NoHash l
        mkAltMatchHaskell (Just bndr) Default = mkIdHaskell pg bndr
        mkAltMatchHaskell _ Default = "_"

mkDataConHaskell :: PrettyGuide -> DataCon -> T.Text
-- Special casing for Data.Map in the modified base
mkDataConHaskell _ (DataCon (Name "Assocs" _ _ _) _) = "fromList"
mkDataConHaskell pg (DataCon n _) = mkNameHaskell pg n

offset :: Int -> T.Text
offset i = duplicate "   " i

printList :: PrettyGuide -> Expr -> T.Text
printList pg a =
    let (strs, b) = printList' pg a
    in case b of
        False -> "(" <> T.intercalate ":" strs <> ")"
        _ -> "[" <> T.intercalate ", " strs <> "]"

printList' :: PrettyGuide -> Expr -> ([T.Text], Bool)
printList' pg (App (App e1 e) e') | Data (DataCon n1 _) <- e1
                                  , nameOcc n1 == ":" =
    let (strs, b) = printList' pg e'
    in (mkExprHaskell Cleaned pg e:strs, b)
printList' pg e | Data (DataCon n _) <- appCenter e
                , nameOcc n == "[]" = ([], True)
                | otherwise = ([mkExprHaskell Cleaned pg e], False)

printString :: PrettyGuide -> Expr -> T.Text
printString pg a =
    let
        maybe_str = printString' a
    in case maybe_str of
        Just str -> if T.all isPrint str then "\"" <> str <> "\""
                    else "[" <> T.intercalate ", " (map (T.pack . stringToEnum) $ T.unpack str) <> "]"
        Nothing -> printList pg a
    where
        stringToEnum c
            | isPrint c = '\'':c:'\'':[]
            | otherwise = "toEnum " ++ show (ord c)

printString' :: Expr -> Maybe T.Text
printString' (App (App _ (Lit (LitChar c))) e') =
    case printString' e' of
        Nothing -> Nothing
        Just str -> Just (T.cons c str)
printString' e | Data (DataCon n _) <- appCenter e
               , nameOcc n == "[]" = Just ""
               | otherwise = Nothing

isTuple :: Name -> Bool
isTuple (Name n _ _ _) = fmap fst (T.uncons n) == Just '(' && fmap snd (T.unsnoc n) == Just ')'
                     && T.all (\c -> c == '(' || c == ')' || c == ',') n

isPrimTuple :: Name -> Bool
isPrimTuple (Name n _ _ _) = fmap fst (T.uncons n) == Just '(' && fmap snd (T.unsnoc n) == Just ')'
                     && T.all (\c -> c == '(' || c == ')' || c == ',' || c == '#') n
                     && T.any (\c -> c == '#') n

printTuple :: PrettyGuide -> Expr -> T.Text
printTuple pg a = "(" <> T.intercalate ", " (reverse $ printTuple' pg a) <> ")"

printPrimTuple :: PrettyGuide -> Expr -> T.Text
printPrimTuple pg a = "(#" <> T.intercalate ", " (reverse $ printTuple' pg a) <> "#)"

printTuple' :: PrettyGuide -> Expr -> [T.Text]
printTuple' pg (App e e') = mkExprHaskell Cleaned pg e':printTuple' pg e
printTuple' _ _ = []

isInfixable :: PrettyGuide -> Expr -> Bool
isInfixable _ (Var (Id n _)) = isInfixableName n
isInfixable _ (Data (DataCon n _)) = isInfixableName n
isInfixable pg (Prim p _) = not . T.any isAlphaNum $ mkPrimHaskellNoDistFloat pg p
isInfixable _ _ = False

isInfixableName :: Name -> Bool
isInfixableName = not . T.any isAlphaNum . nameOcc

isApp :: Expr -> Bool
isApp (App _ _) = True
isApp _ = False

isLitChar :: Expr -> Bool
isLitChar (Lit (LitChar _)) = True
isLitChar _ = False

data UseHash = UseHash | NoHash deriving Eq

mkLitHaskell :: UseHash -> Lit -> T.Text
mkLitHaskell use = lit
    where
        hs = if use == UseHash then "#" else ""

        lit (LitInt i) = T.pack $ if i < 0 then "(" <> show i <> hs <> ")" else show i <> hs
        lit (LitInteger i) = T.pack $ if i < 0 then "(" <> show i <> hs <> ")" else show i <> hs
        lit (LitFloat r) = mkFloat (T.pack hs) r
        lit (LitDouble r) = mkFloat (T.pack hs) r
        lit (LitRational r) = "(" <> T.pack (show r) <> ")"
        lit (LitChar c) | isPrint c = T.pack ['\'', c, '\'']
                        | otherwise = "(chr " <> T.pack (show $ ord c) <> ")"
        lit (LitString s) = T.pack s

mkFloat :: (Show n, RealFloat n) => T.Text -> n -> T.Text
mkFloat hs r | isNaN r = "(0" <> hs <> " / 0" <> hs <> ")"
             | r == 1 / 0 = "(1" <> hs <> " / 0" <> hs <> ")" -- Infinity
             | r == -1 / 0 = "(-1" <> hs <> " / 0" <> hs <> ")" -- Negative Infinity
             | otherwise = "(" <> T.pack (show r) <> hs <> ")"

mkPrimHaskell :: PrettyGuide -> Primitive -> T.Text
mkPrimHaskell pg = pr
    where
        pr Ge = ">="
        pr Gt = ">"
        pr Eq = "=="
        pr Neq = "/="
        pr Lt = "<"
        pr Le = "<="
        pr And = "&&"
        pr Or = "||"
        pr Not = "not"
        pr Plus = "+"
        pr Minus = "-"
        pr Mult = "*"
        pr Div = "/"
        pr DivInt = "/"
        pr Quot = "quot"
        pr Mod = "mod"
        pr Rem = "rem"
        pr Negate = "-"
        pr Abs = "abs"

        pr Sqrt = "sqrt"

        pr FpNeg = "fp.-"
        pr FpAdd = "fp.+"
        pr FpSub = "fp.-"
        pr FpMul = "fp.*"
        pr FpDiv = "fp./"
        pr FpLeq = "fp.<="
        pr FpLt = "fp.<"
        pr FpGeq = "fp.>="
        pr FpGt = "fp.>"
        pr FpEq = "fp.=="
        pr FpNeq = "fp./="

        pr FpSqrt = "fp.sqrt"

        pr FpIsNegativeZero = "isNegativeZero#"
        pr IsNaN = "isNaN#"
        pr IsInfinite = "isInfinite#"

        pr DataToTag = "prim_dataToTag#"
        pr TagToEnum = "prim_tagToEnum#"


        pr IntToFloat = "fromIntegral"
        pr IntToDouble = "fromIntegral"
        pr IntToRational = "fromIntegral"
        pr RationalToFloat = "fromRational"
        pr RationalToDouble = "fromRational"
        pr ToInteger = "toInteger"

        pr StrLen = "StrLen"
        pr StrAppend = "StrAppend"
        pr Chr = "chr"
        pr OrdChar = "ord"

        pr WGenCat = "wgencat"

        pr IntToString = "intToString"

        pr (MutVar m) = "(MutVar " <> mkNameHaskell pg m <> ")"
        pr NewMutVar = "newMutVar##"
        pr ReadMutVar = "readMutVar##"
        pr WriteMutVar = "writeMutVar##"

        pr ToInt = "toInt"

        pr Error = "error"
        pr Undefined = "undefined"
        pr Implies = "undefined"
        pr Iff = "undefined"

mkPrimHaskellNoDistFloat :: PrettyGuide -> Primitive -> T.Text
mkPrimHaskellNoDistFloat pg = pr
    where
        pr FpNeg = "-"
        pr FpAdd = "+"
        pr FpSub = "-"
        pr FpMul = "*"
        pr FpDiv = "/"
        pr FpLeq = "<="
        pr FpLt = "<"
        pr FpGeq = ">="
        pr FpGt = ">"
        pr FpEq = "=="
        pr FpNeq = "/="
        pr FpSqrt = "sqrt"
        pr p = mkPrimHaskell pg p

mkTypeHaskell :: Type -> T.Text
mkTypeHaskell = mkTypeHaskellPG (mkPrettyGuide ())

mkTypeHaskellPG :: PrettyGuide -> Type -> T.Text
mkTypeHaskellPG pg (TyVar i) = mkIdHaskell pg i
mkTypeHaskellPG _ TyLitInt = "Int#"
mkTypeHaskellPG _ TyLitFloat = "Float#"
mkTypeHaskellPG _ TyLitDouble = "Double#"
mkTypeHaskellPG _ TyLitRational = "Rational#"
mkTypeHaskellPG _ TyLitChar = "Char#"
mkTypeHaskellPG _ TyLitString = "String#"
mkTypeHaskellPG pg (TyFun t1 t2)
    | isTyFun t1 = "(" <> mkTypeHaskellPG pg t1 <> ") -> " <> mkTypeHaskellPG pg t2
    | otherwise = mkTypeHaskellPG pg t1 <> " -> " <> mkTypeHaskellPG pg t2
mkTypeHaskellPG pg (TyCon n _) | nameOcc n == "List"
                               , nameModule n == Just "GHC.Types" = "[]"
                               | otherwise = mkNameHaskell pg n
mkTypeHaskellPG pg (TyApp t1 t2) = "(" <> mkTypeHaskellPG pg t1 <> " " <> mkTypeHaskellPG pg t2 <> ")"
mkTypeHaskellPG pg (TyForAll i t) = "forall " <> mkIdHaskell pg i <> " . " <> mkTypeHaskellPG pg t
mkTypeHaskellPG _ TyBottom = "Bottom"
mkTypeHaskellPG _ TYPE = "Type"
mkTypeHaskellPG _ (TyUnknown) = "Unknown"

duplicate :: T.Text -> Int -> T.Text
duplicate _ 0 = ""
duplicate s n = s <> duplicate s (n - 1)

printTickish :: PrettyGuide -> Tickish -> T.Text
printTickish _ (Breakpoint sp) = printLoc (start sp) <> " - " <> printLoc (end sp)
printTickish _ (HpcTick i m) = "(hpc " <> T.pack (show i) <> " " <> m <> ")" 
printTickish pg (NamedLoc n) = mkNameHaskell pg n

printLoc :: Loc -> T.Text
printLoc (Loc ln cl fl) = "(line " <> T.pack (show ln) <> " column " <> T.pack (show cl) <> " in " <>  T.pack fl <> ")" 

-------------------------------------------------------------------------------

prettyState :: Show t => PrettyGuide -> State t -> T.Text
prettyState pg s =
    T.intercalate "\n"
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
        , "----- [MutVars Env] ---------------------"
        , pretty_mutvars
        , "----- [Types] ---------------------"
        , pretty_tenv
        , "----- [Typeclasses] ---------------------"
        , pretty_tc
        , "----- [True Assert] ---------------------"
        , T.pack (show (true_assert s))
        , "----- [Assert FC] ---------------------"
        , pretty_assert_fcs
        , "----- [Tracker] ---------------------"
        , T.pack (show (track s))
        , "----- [Pretty] ---------------------"
        , pretty_names
        ]
    where
        pretty_curr_expr = prettyCurrExpr pg (curr_expr s)
        pretty_stack = prettyStack pg (exec_stack s)
        pretty_eenv = prettyEEnv pg (expr_env s)
        pretty_paths = prettyPathConds pg (path_conds s)
        pretty_non_red_paths = prettyNonRedPaths pg (non_red_path_conds s)
        pretty_mutvars = prettyMutVars pg . HM.map mv_val_id $ mutvar_env s
        pretty_tenv = prettyTypeEnv pg (type_env s)
        pretty_tc = prettyTypeClasses pg (type_classes s)
        pretty_assert_fcs = maybe "None" (printFuncCallPG pg) (assert_ids s)
        pretty_names = prettyGuideStr pg


prettyCurrExpr :: PrettyGuide -> CurrExpr -> T.Text
prettyCurrExpr pg (CurrExpr er e) =
    let
        e_str = mkDirtyExprHaskell pg e
    in
    case er of
        Evaluate -> "evaluate: " <> e_str
        Return -> "return: " <> e_str

prettyStack :: PrettyGuide -> Stack Frame -> T.Text
prettyStack pg = T.intercalate "\n" . map (prettyFrame pg) . toList

prettyFrame :: PrettyGuide -> Frame -> T.Text
prettyFrame pg (CaseFrame i _ as) =
    "case frame: bindee:" <> mkIdHaskell pg i <> "\n" <> T.intercalate "\n" (map (mkAltHaskell 1 Dirty pg i) as)
prettyFrame pg (ApplyFrame e) = "apply frame: " <> mkDirtyExprHaskell pg e
prettyFrame pg (UpdateFrame n) = "update frame: " <> mkNameHaskell pg n
prettyFrame pg (CastFrame (t1 :~ t2)) = "cast frame: " <> mkTypeHaskellPG pg t1 <> " ~ " <> mkTypeHaskellPG pg t2
prettyFrame pg (CurrExprFrame act ce) = "curr_expr frame: " <> prettyCEAction pg act <> prettyCurrExpr pg ce
prettyFrame pg (AssumeFrame e) = "assume frame: " <> mkDirtyExprHaskell pg e
prettyFrame pg (AssertFrame m_fc e) =
    let
        fc = case m_fc of
                  Just fc_ -> "(from call " <> printFuncCallPG pg fc_ <> ")"
                  Nothing -> ""
    in
    "assert frame: " <> fc <> mkDirtyExprHaskell pg e

prettyCEAction :: PrettyGuide -> CEAction -> T.Text
prettyCEAction pg (EnsureEq e) = "EnsureEq " <> mkDirtyExprHaskell pg e
prettyCEAction _ NoAction = "NoAction"

prettyEEnv :: PrettyGuide -> ExprEnv -> T.Text
prettyEEnv pg eenv = T.intercalate "\n\n"
                   . map (uncurry printFunc)
                   . E.toList $ eenv
    where
        printFunc n e = mkNameHaskell pg n <> " :: " <> mkTypeHaskellPG pg (envObjType eenv e)
                            <> "\n" <> mkNameHaskell pg n <> " = " <> printEnvObj pg e

printEnvObj :: PrettyGuide -> E.EnvObj -> T.Text
printEnvObj pg (E.ExprObj e) = mkDirtyExprHaskell pg e
printEnvObj pg (E.SymbObj (Id _ t)) = "symbolic " <> mkTypeHaskellPG pg t
printEnvObj pg (E.RedirObj n) = "redir to " <> mkNameHaskell pg n

envObjType :: ExprEnv -> E.EnvObj -> Type
envObjType _ (E.ExprObj e) = typeOf e
envObjType _ (E.SymbObj (Id _ t)) = t
envObjType eenv (E.RedirObj n) = maybe (TyCon (Name "???" Nothing 0 Nothing) TYPE) typeOf $ E.lookup n eenv

prettyPathConds :: PrettyGuide -> PathConds -> T.Text
prettyPathConds pg = T.intercalate "\n" . map (prettyPathCond pg) . PC.toList

prettyPathCond :: PrettyGuide -> PathCond -> T.Text
prettyPathCond pg (AltCond l e b) =
    let
        eq = mkLitHaskell NoHash l <> " = " <> mkDirtyExprHaskell pg e
    in
    if b then eq else "not (" <> eq <> ")"
prettyPathCond pg (ExtCond e b) =
    if b then mkDirtyExprHaskell pg e else "not (" <> mkDirtyExprHaskell pg e <> ")"
prettyPathCond pg (SoftPC pc) =
    "soft (" <> prettyPathCond pg pc <> ")"
prettyPathCond pg (MinimizePC e) =
    "minimize (" <> mkDirtyExprHaskell pg e <> ")"
prettyPathCond pg (AssumePC i l pc) =
    let
        pc' = map PC.unhashedPC $ HS.toList pc
    in
    mkIdHaskell pg i <> " = " <> T.pack (show l) <> "=> (" <> T.intercalate "\nand " (map (prettyPathCond pg) pc') <> ")"

prettyNonRedPaths :: PrettyGuide -> [(Expr, Expr)] -> T.Text
prettyNonRedPaths pg = T.intercalate "\n" . map (\(e1, e2) -> mkDirtyExprHaskell pg e1 <> " == " <> mkDirtyExprHaskell pg e2)

prettyMutVars :: PrettyGuide -> HM.HashMap Name Id -> T.Text
prettyMutVars pg = T.intercalate "\n" . map (\(n, i) -> printName pg n <> " , " <> mkIdHaskell pg i) . HM.toList

prettyTypeEnv :: PrettyGuide -> TypeEnv -> T.Text
prettyTypeEnv pg = T.intercalate "\n" . map (uncurry (prettyADT pg)) . HM.toList

prettyADT :: PrettyGuide -> Name -> AlgDataTy -> T.Text
prettyADT pg n DataTyCon { bound_ids = bids, data_cons = dcs } =
    "data " <> mkNameHaskell pg n <> " "
            <> T.intercalate " " (map (mkIdHaskell pg) bids)
            <> " = " <> T.intercalate " | " (map (prettyDCWithType pg) dcs)
prettyADT pg n NewTyCon { bound_ids = bids, data_con = dc } =
    "newtype " <> mkNameHaskell pg n <> " "
               <> T.intercalate " " (map (mkIdHaskell pg) bids)
               <> " = " <> prettyDCWithType pg dc
prettyADT pg n TypeSynonym { bound_ids = bids, synonym_of = t } =
    "type " <> mkNameHaskell pg n <> " "
            <> T.intercalate " " (map (mkIdHaskell pg) bids)
            <> " = " <> mkTypeHaskellPG pg t

prettyDCWithType :: PrettyGuide -> DataCon -> T.Text
prettyDCWithType pg dc = mkDataConHaskell pg dc <> " :: " <> mkTypeHaskellPG pg (typeOf dc)

prettyTypeClasses :: PrettyGuide -> TypeClasses -> T.Text
prettyTypeClasses pg = T.intercalate "\n" . map (\(n, tc) -> mkNameHaskell pg n <> " = " <> prettyClass pg tc) . HM.toList . toMap

prettyClass :: PrettyGuide -> Class -> T.Text
prettyClass pg cls =
    let
        sc = T.intercalate ", " $ map (\(t, i) -> mkTypeHaskellPG pg t <> " " <> mkIdHaskell pg i) (superclasses cls)
        ti = T.intercalate " " . map (mkIdHaskell pg) $ typ_ids cls
        ins = T.intercalate "\n\t\t" $ map (\(t, i) -> mkTypeHaskellPG pg t <> " " <> mkIdHaskell pg i) (insts cls)
    in
       "\n\tsuper_classes = " <> sc
    <> "\n\ttype_ids = " <> ti
    <> "\n\tinsts = " <> ins

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

printFuncCall :: FuncCall -> T.Text
printFuncCall = printFuncCallPG (mkPrettyGuide ())

printFuncCallPG :: PrettyGuide -> FuncCall -> T.Text
printFuncCallPG pg (FuncCall { funcName = f, arguments = ars, returns = r}) =
    let
        call_str fn = mkDirtyExprHaskell pg . foldl (\a a' -> App a a') (Var (Id fn TyUnknown)) $ ars
        r_str = mkDirtyExprHaskell pg r
    in
    "(" <> call_str f <> " " <> r_str <> ")"

-------------------------------------------------------------------------------
-- Pretty Guide
-------------------------------------------------------------------------------

-- | Maps G2 `Name`s to printable `String`s uniquely and consistently
-- (two `Name`s will not map to the same `String`, and on a per `PrettyGuide`
-- basis the same `Name` will always map to the same `String`.)
-- The `PrettyGuide` will only work on `Name`s it "knows" about.
-- It "knows" about names in the `Named` value it is passed in it's creation
-- (via `mkPrettyGuide`) and all `Name`s that it is passed via `updatePrettyGuide`.
data PrettyGuide = PG { pg_assigned :: HM.HashMap Name T.Text, pg_nums :: HM.HashMap T.Text Int }

mkPrettyGuide :: Named a => a -> PrettyGuide
mkPrettyGuide = foldr insertPG (PG HM.empty HM.empty) . names

updatePrettyGuide :: Named a => a -> PrettyGuide -> PrettyGuide
updatePrettyGuide ns pg = foldr insertPG pg $ names ns

insertPG :: Name -> PrettyGuide -> PrettyGuide
insertPG n pg@(PG { pg_assigned = as, pg_nums = nms })
    | not (HM.member n as) =
        case HM.lookup (nameOcc n) nms of
            Just i ->
                PG { pg_assigned = HM.insert n (nameOcc n <> "'" <> T.pack (show i)) as
                   , pg_nums = HM.insert (nameOcc n) (i + 1) nms }
            Nothing ->
                PG { pg_assigned = HM.insert n (nameOcc n) as
                   , pg_nums = HM.insert (nameOcc n) 1 nms }
    | otherwise = pg

lookupPG :: Name -> PrettyGuide -> Maybe T.Text
lookupPG n = HM.lookup n . pg_assigned

prettyGuideStr :: PrettyGuide -> T.Text
prettyGuideStr = T.intercalate "\n" . map (\(n, s) -> s <> " <-> " <> T.pack (show n)) . HM.toList . pg_assigned
