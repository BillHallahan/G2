module G2.Lib.Printers where

import G2.Internals.Core.Language

import qualified Data.List as L
import qualified Data.Map as M

sp2 :: String
sp2 = "  "

sp4 :: String
sp4 = sp2 ++ sp2

mkRawStateStr :: State -> String
mkRawStateStr state = L.intercalate "\n" li
  where tenv_str  = L.intercalate "\n" $ map show $ M.toList $ type_env state
        eenv_str  = L.intercalate "\n" $ map show $ M.toList $ expr_env state
        cexpr_str = show $ curr_expr state
        pc_str    = L.intercalate "\n" $ map show $ path_cons state
        slt_str   = show $ sym_links state
        fintp_str = show $ func_interps state
        dashes = "------"
        li = [ "BEGIN STATE"
             , "[type_env]",     tenv_str,  dashes
             , "[expr_env]",     eenv_str,  dashes
             , "[curr_expr]",    cexpr_str, dashes
             , "[path_cons]",    pc_str,    dashes
             , "[sym_links]",    slt_str,   dashes
             , "[func_interps]", fintp_str
             , "END STATE" ]


mkStateStr :: State -> String
mkStateStr s = L.intercalate "\n\n" li
  where li = ["> Type Env:\n" ++ ts,  "> Expr Env:\n" ++ es
             ,"> Curr Expr:\n" ++ xs, "> Path Constraints:\n" ++ ps
             ,"> Sym Link Table:\n" ++ sl
             ,"> Func Sym Link Table:\n" ++ fl]
        ts = mkTypexpr_envStr . type_env $ s
        es = mkExprEnvStr . expr_env $ s
        xs = mkExprStr . curr_expr $ s
        ps = mkPCStr . path_cons $ s
        sl = mkSLTStr . sym_links $ s
        fl = mkFuncSLTStr . func_interps $ s

mkStatesStr :: [State] -> String
mkStatesStr []     = ""
mkStatesStr [s] = mkStateStr s
mkStatesStr (s:ss) = mkStateStr s ++ divLn ++ mkStatesStr ss
  where divLn = "\n--------------\n"

mkTypexpr_envStr :: TEnv -> String
mkTypexpr_envStr tenv = L.intercalate "\n" (map ntStr (M.toList tenv))
  where ntStr :: (Name, Type) -> String
        ntStr (n, t) = n ++ "\n" ++ sp4 ++ show t

mkExprEnvStr :: EEnv -> String
mkExprEnvStr eenv = L.intercalate "\n" (map neStr (M.toList eenv))
  where neStr :: (Name, Expr) -> String
        neStr (n, e) = n ++ "\n" ++ sp4 ++ mkExprStr e


mkExprStr :: Expr -> String
mkExprStr e = mkExprStr' e 0
    where
        mkExprStr' :: Expr -> Int -> String
        mkExprStr' (Var n t) i = off i ++ "Var " ++ n ++ " (" ++ mkTypeStr t (i + 1) ++")"
        mkExprStr' (Lam n e t) i = 
            let
                e' = mkExprStr' e (i + 1)
            in
            off i ++  "Lam (" ++ show n ++ "\n" ++ e' ++ " " ++ mkTypeStr t i ++")"
        mkExprStr' (App e1 e2) i = 
            let
                e1' = mkExprStr' e1 (i + 1)
                e2' = mkExprStr' e2 (i + 1)
            in
            off i ++ "App (\n" ++ e1' ++ "\n" ++ e2' ++ "\n" ++ off i ++ ")"
        mkExprStr' (Case e1 ae t) i = 
            let
                e1' = mkExprStr' e1 (i + 1)
                ae' = mkAltExprStr ae (i + 1)
            in
            off i ++ "Case (\n" ++ e1' ++ "\n" ++ ae' ++ " " ++ mkTypeStr t i ++ ")"
        mkExprStr' (Type t) i = off i ++ "Type (" ++ mkTypeStr t (i + 1) ++ ")"
        mkExprStr' x i = off i ++ show x


        mkAltExprStr :: [(Alt, Expr)] -> Int -> String
        mkAltExprStr [] _ = ""
        mkAltExprStr ((a, e):xs) i = off i ++ "(" ++ show a ++ ",\n" ++ 
                                        mkExprStr' e (i + 1) ++ ")\n" ++ mkAltExprStr xs i

        off :: Int -> String
        off i = duplicate "   " i


mkTypeStr :: Type -> Int -> String
mkTypeStr t i = mkTypeStr' t i False
    where
        mkTypeStr' :: Type -> Int -> Bool -> String
        mkTypeStr' (TyFun t1 t2) i  b = tPat t1 t2 "TyFun" i b 
        mkTypeStr' (TyApp t1 t2) i  b = tPat t1 t2 "TyApp" i b 
        mkTypeStr' (TyConApp n tx) i b = 
            let li = L.intercalate ", " . map (\t' -> mkTypeStr' t' (i + 1) b) $ tx in
                off i b ++ "TyConApp " ++ show n ++ " [" ++ li ++ "]"
        mkTypeStr' (TyForAll n t) i b = off i b ++ "TyForAll " ++ show n ++
                                        "(" ++ mkTypeStr' t (i + 1) b ++ ")"
        mkTypeStr' t i b = (if b then " " else "") ++ show t

        tPat :: Type -> Type -> String -> Int -> Bool -> String
        tPat t1 t2 s i b = off i b ++ s ++ " (" 
                            ++ mkTypeStr' t1 (i + 1) True 
                            ++ mkTypeStr' t2 (i + 1) True ++ off i True ++  ")"

        off :: Int -> Bool -> String
        off i b = if b then "\n" ++ duplicate "   " i else ""


-- Primitive for now because I'm low on battery.
mkPCStr :: PathCons -> String
mkPCStr [] = ""
mkPCStr [(e, a, b)] = mkExprStr e ++ (if b then " = " else " != ") ++ show a
mkPCStr ((e, a, b):ps) = mkExprStr e ++ (if b then " = " else " != ") ++ show a++ "\n--AND--\n" ++ mkPCStr ps

mkSLTStr :: SymLinkTable -> String
mkSLTStr = L.intercalate "\n" . map (\(k, (n, t, i)) -> 
                                                k ++ " <- " ++ n ++ "  (" ++ show t ++ ")"
                                                ++ case i of
                                                        Just x -> "  " ++ show x
                                                        Nothing -> "") . M.toList

mkFuncSLTStr :: FuncInterpTable -> String
mkFuncSLTStr = L.intercalate "\n" . map (\(k, (n, i)) -> k ++ " <- " ++ n ++ "  " ++ show i) . M.toList

mkExprHaskell :: Expr -> String
mkExprHaskell e = mkExprHaskell' e 0
    where 
        mkExprHaskell' :: Expr -> Int -> String
        mkExprHaskell' (Var n _) _ = n
        mkExprHaskell' (Const c) _ = mkConstHaskell c
        mkExprHaskell' (Lam n e _) i = "\\" ++ n ++ " -> " ++ mkExprHaskell' e i
        mkExprHaskell' (App e1 e2@(App _ _)) i = mkExprHaskell' e1 i ++ " (" ++ mkExprHaskell' e2 i ++ ")"
        mkExprHaskell' (App e1 e2) i = mkExprHaskell' e1 i ++ " " ++ mkExprHaskell' e2 i
        mkExprHaskell' (Data (DataCon n _ _ _)) _ = n
        mkExprHaskell' (Case e ae _) i = off (i + 1) ++ "\ncase " ++ (mkExprHaskell' e i) ++ " of\n" 
                                        ++ L.intercalate "\n" (map (mkAltExprHaskell (i + 2)) ae)
        mkExprHaskell' (Type _) _ = ""
        mkExprHaskell' BAD _ = "BAD"

        mkAltExprHaskell :: Int -> (Alt, Expr) -> String
        mkAltExprHaskell i (Alt (DataCon n _ _ _, n'), e) = off i ++ n ++ " " ++ L.intercalate " " n' ++ " -> " ++ mkExprHaskell' e i

        off :: Int -> String
        off i = duplicate "   " i

mkConstHaskell :: Const -> String
mkConstHaskell (CInt i) = show i
mkConstHaskell (CFloat r) = "(" ++ show r ++ ")"
mkConstHaskell (CDouble r) = "(" ++ show r ++ ")"
mkConstHaskell (CChar c) = [c]
mkConstHaskell (CString s) = s
mkConstHaskell (COp n _) = n

duplicate :: String -> Int -> String
duplicate _ 0 = ""
duplicate s n = s ++ duplicate s (n - 1)
