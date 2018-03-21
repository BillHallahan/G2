{-# LANGUAGE OverloadedStrings #-}

module G2.Lib.Printers ( mkCleanExprHaskell
                       , pprExecStateStr) where

import qualified G2.Internals.Language.ApplyTypes as AT
import G2.Internals.Language.Expr
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.KnownValues
import G2.Internals.Language.Naming
import qualified G2.Internals.Language.PathConds as PC
import G2.Internals.Language.TypeClasses
import G2.Internals.Language.Typing
import G2.Internals.Language.Stack
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support

import Data.Char
import Data.Coerce
import Data.List
import qualified Data.Map as M
import qualified Data.Text as T

mkIdHaskell :: Id -> String
mkIdHaskell (Id n _) = mkNameHaskell n

mkNameHaskell :: Name -> String
mkNameHaskell (Name n _ _) = T.unpack n

mkCleanExprHaskell :: State h t -> Expr -> String
mkCleanExprHaskell (State {apply_types = af, known_values = kv, type_classes = tc}) =
    mkExprHaskell kv . modifyFix (mkCleanExprHaskell' af kv tc)

mkCleanExprHaskell' :: AT.ApplyTypes -> KnownValues -> TypeClasses -> Expr -> Expr
mkCleanExprHaskell' at kv tc e
    | (App (Data (DataCon n _ _)) e') <- e
    , n == dcInt kv || n == dcFloat kv || n == dcDouble kv || n == dcInteger kv = e'
    | (App e' e'') <- e
    , t <- typeOf e'
    , TyConApp n _ <- t
    , isTypeClassNamed n tc = e''
    | (App e' e'') <- e
    , t <- typeOf e''
    , TyConApp n _ <- t
    , isTypeClassNamed n tc = e'
    | App e' (Type _) <- e = e'
    | App _ e'' <- e
    , (Var (Id n _)) <- appCenter e
    , n `elem` map idName (AT.applyFuncs at) = e''
    | otherwise = e

mkExprHaskell :: KnownValues -> Expr -> String
mkExprHaskell kv ex = mkExprHaskell' ex 0
    where
        mkExprHaskell' :: Expr -> Int -> String
        mkExprHaskell' (Var ids) _ = mkIdHaskell ids
        mkExprHaskell' (Lit c) _ = mkLitHaskell c
        mkExprHaskell' (Prim p _) _ = mkPrimHaskell p
        mkExprHaskell' (Lam ids e) i = "\\" ++ mkIdHaskell ids ++ " -> " ++ mkExprHaskell' e i
        mkExprHaskell' a@(App ea@(App e1 e2) e3) i
            | Data (DataCon n _ _) <- appCenter a
            , isTuple n = printTuple kv a
            | Data (DataCon n1 _ _) <- e1
            , nameOccStr n1 == ":" =
                case typeOf e2 of
                    TyLitChar -> printString a
                    _ -> printList kv a
            | isInfixable e1 =
                let
                    e2P = if isApp e2 then "(" ++ mkExprHaskell' e2 i ++ ")" else mkExprHaskell' e2 i
                    e3P = if isApp e3 then "(" ++ mkExprHaskell' e3 i ++ ")" else mkExprHaskell' e3 i
                in
                e2P ++ " " ++ mkExprHaskell' e1 i ++ " " ++ e3P
            | App _ _ <- e3 = mkExprHaskell' ea i ++ " (" ++ mkExprHaskell' e3 i ++ ")"
            | otherwise = mkExprHaskell' ea i ++ " " ++ mkExprHaskell' e3 i
        mkExprHaskell' (App e1 ea@(App _ _)) i = mkExprHaskell' e1 i ++ " (" ++ mkExprHaskell' ea i ++ ")"
        mkExprHaskell' (App e1 e2) i = mkExprHaskell' e1 i ++ " " ++ mkExprHaskell' e2 i
        mkExprHaskell' (Data d) _ = mkDataConHaskell d
        mkExprHaskell' (Case e _ ae) i = off (i + 1) ++ "\ncase " ++ (mkExprHaskell' e i) ++ " of\n" 
                                        ++ intercalate "\n" (map (mkAltHaskell (i + 2)) ae)
        mkExprHaskell' (Type _) _ = ""
        mkExprHaskell' (Cast e (_ :~ t)) i = "((coerce " ++ mkExprHaskell' e i ++ ") :: " ++ mkTypeHaskell t ++ ")"
        mkExprHaskell' e _ = "e = " ++ show e ++ " NOT SUPPORTED"

        mkAltHaskell :: Int -> Alt -> String
        mkAltHaskell i (Alt am e) =
            off i ++ mkAltMatchHaskell am ++ " -> " ++ mkExprHaskell' e i

        mkAltMatchHaskell :: AltMatch -> String
        mkAltMatchHaskell (DataAlt dc ids) = mkDataConHaskell dc ++ " " ++ intercalate " "  (map mkIdHaskell ids)
        mkAltMatchHaskell (LitAlt l) = mkLitHaskell l
        mkAltMatchHaskell Default = "_"

        mkDataConHaskell :: DataCon -> String
        -- Special casing for Data.Map in the modified base
        mkDataConHaskell (DataCon (Name "Assocs" _ _) _ _) = "fromList"
        mkDataConHaskell (DataCon n _ _) = mkNameHaskell n

        off :: Int -> String
        off i = duplicate "   " i

printList :: KnownValues -> Expr -> String
printList kv a = "[" ++ intercalate ", " (printList' kv a) ++ "]"

printList' :: KnownValues -> Expr -> [String]
printList' kv (App (App _ e) e') = mkExprHaskell kv e:printList' kv e'
printList' _ _ = []

printString :: Expr -> String
printString a = "\"" ++ printString' a ++ "\""

printString' :: Expr -> String
printString' (App (App _ (Lit (LitChar c))) e') = c:printString' e'
printString' _ = []

isTuple :: Name -> Bool
isTuple (Name n _ _) = T.head n == '(' && T.last n == ')'
                     && T.all (\c -> c == '(' || c == ')' || c == ',') n

printTuple :: KnownValues -> Expr -> String
printTuple kv a = "(" ++ intercalate ", " (reverse $ printTuple' kv a) ++ ")"

printTuple' :: KnownValues -> Expr -> [String]
printTuple' kv (App e e') = mkExprHaskell kv e':printTuple' kv e
printTuple' _ _ = []


isInfixable :: Expr -> Bool
isInfixable (Data (DataCon (Name n _ _) _ _)) = not $ T.any isAlphaNum n
isInfixable _ = False

isApp :: Expr -> Bool
isApp (App _ _) = True
isApp _ = False

mkLitHaskell :: Lit -> String
mkLitHaskell (LitInt i) = show i
mkLitHaskell (LitInteger i) = show i
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
mkPrimHaskell Negate = "-"
mkPrimHaskell SqRt = "sqrt"
mkPrimHaskell IntToFloat = "fromIntegral"
mkPrimHaskell IntToDouble = "fromIntegral"
mkPrimHaskell FromInteger = "fromInteger"
mkPrimHaskell ToInteger = "toInteger"
mkPrimHaskell Error = "error"
mkPrimHaskell Undefined = "undefined"
mkPrimHaskell Implies = "undefined"
mkPrimHaskell Iff = "undefined"

mkTypeHaskell :: Type -> String
mkTypeHaskell (TyVar i) = mkIdHaskell i
mkTypeHaskell (TyFun t1 t2) = mkTypeHaskell t1 ++ " -> " ++ mkTypeHaskell t2
mkTypeHaskell (TyConApp n ts) = mkNameHaskell n ++ " " ++ (intercalate " " $ map mkTypeHaskell ts)
mkTypeHaskell _ = "Unsupported type in printer."

duplicate :: String -> Int -> String
duplicate _ 0 = ""
duplicate s n = s ++ duplicate s (n - 1)

injNewLine :: [String] -> String
injNewLine strs = intercalate "\n" strs

injTuple :: [String] -> String
injTuple strs = "(" ++ (intercalate "," strs) ++ ")"

-- | More raw version of state dumps.
pprExecStateStr :: State h t -> String
pprExecStateStr ex_state = injNewLine acc_strs
  where
    eenv_str = pprExecEEnvStr (expr_env ex_state)
    tenv_str = pprTEnvStr (type_env ex_state)
    estk_str = pprExecStackStr (exec_stack ex_state)
    code_str = pprExecCodeStr (curr_expr ex_state)
    names_str = pprExecNamesStr (name_gen ex_state)
    input_str = pprInputIdsStr (symbolic_ids ex_state)
    funcs_str = pprFuncTableStr (func_table ex_state)
    paths_str = pprPathsStr (PC.toList $ path_conds ex_state)
    tc_str = pprTCStr (type_classes ex_state)
    walkers_str = show (deepseq_walkers ex_state)
    appty_str = show (apply_types ex_state)
    cleaned_str = pprCleanedNamesStr (cleaned_names ex_state)
    rules_str = intercalate "\n" $ map show (zip ([0..] :: [Integer]) $ rules ex_state)
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
               , "----- [Func Table] ----------------"
               , funcs_str
               , "----- [Walkers] -------------------"
               , walkers_str
               , "----- [Paths] ---------------------"
               , paths_str
               , "----- [True Assert] ---------------------"
               , "True Assert = " ++ show (true_assert ex_state)
               , "----- [Assert Ids] ---------------------"
               , show (assert_ids ex_state)
               , "----- [TypeClasses] ---------------------"
               , tc_str
               , "----- [Apply Types] ---------------------"
               , appty_str
               , "----- [Cleaned] -------------------"
               , cleaned_str
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
    kv_strs = map show $ M.toList tenv

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
    cond_strs = map show $ M.toList $ ((coerce tc) :: M.Map Name Class)

pprInputIdsStr :: InputIds -> String
pprInputIdsStr i = injNewLine id_strs
  where
    id_strs = map show i

pprFuncTableStr :: FuncInterps -> String
pprFuncTableStr (FuncInterps funcs) = injNewLine funcs_strs
  where
    funcs_strs = map show (M.toList funcs)

pprPathCondStr :: PathCond -> String
pprPathCondStr (AltCond am expr b) = injTuple acc_strs
  where
    am_str = show am
    expr_str = show expr
    b_str = show b
    acc_strs = [am_str, expr_str, b_str]
pprPathCondStr (ExtCond am b) = injTuple acc_strs
  where
    am_str = show am
    b_str = show b
    acc_strs = [am_str, b_str]
pprPathCondStr (ConsCond d expr b) = injTuple acc_strs
  where
    d_str = show d
    expr_str = show expr
    b_str = show b
    acc_strs = [d_str, expr_str, b_str]
pprPathCondStr (PCExists p) = show p

pprCleanedNamesStr :: CleanedNames -> String
pprCleanedNamesStr = injNewLine . map show . M.toList

