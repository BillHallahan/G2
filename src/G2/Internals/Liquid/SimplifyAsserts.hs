{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.SimplifyAsserts ( simplifyAsserts
                                           , simplifyAssertsG
                                           , eCheck) where

import G2.Internals.Language
import G2.Internals.Language.KnownValues
import G2.Internals.Liquid.TCValues

type ModifiedKnownValues = KnownValues

simplifyAsserts :: ASTContainer t Expr => ModifiedKnownValues -> TCValues -> State t -> State t
simplifyAsserts mkv tcv s@(State {type_env = tenv, known_values = kv}) =
    modifyASTs (simplifyAsserts' tenv kv mkv tcv) s

simplifyAssertsG :: ASTContainer m Expr => KnownValues -> TCValues -> TypeEnv -> KnownValues -> m -> m
simplifyAssertsG mkv tcv tenv kv = modifyASTs (simplifyIn tenv kv mkv tcv)

simplifyAsserts' :: TypeEnv -> KnownValues -> ModifiedKnownValues -> TCValues -> Expr -> Expr
simplifyAsserts' tenv kv mkv tcv (Assume a e) = Assume (simplifyIn tenv kv mkv tcv a) e
simplifyAsserts' tenv kv mkv tcv (Assert i a e) = Assert i (simplifyIn tenv kv mkv tcv a) e
simplifyAsserts' _ _ _ _ e = e

simplifyIn :: TypeEnv -> KnownValues -> ModifiedKnownValues -> TCValues -> Expr -> Expr
simplifyIn tenv kv mkv tcv e =
    -- simplifyIn' tenv kv mkv e
    let
        e' = simplifyIn' tenv kv mkv tcv e
    in
    if e == e' then e else simplifyIn tenv kv mkv tcv e'

simplifyIn' :: TypeEnv -> KnownValues -> ModifiedKnownValues -> TCValues -> Expr -> Expr
-- simplifyIn' tenv kv mkv tcv = elimAnds tenv kv mkv . elimLHPP tenv kv tcv . varBetaReduction
simplifyIn' tenv kv mkv tcv = elimAnds tenv kv mkv . varBetaReduction


elimAnds :: TypeEnv -> KnownValues -> ModifiedKnownValues -> Expr -> Expr
elimAnds tenv kv mkv = elimCalls2 (andFunc mkv) (mkTrue kv tenv)

elimLHPP :: TypeEnv -> KnownValues -> TCValues -> Expr -> Expr
elimLHPP tenv kv tcv a@(App e e') =
    case isNestedLPP tcv a of
        True -> case isRedundantNestedArg kv tcv a of
                    True -> mkTrue kv tenv
                    False -> App (modifyAppRHS (elimLHPP tenv kv tcv) e) (elimLHPP tenv kv tcv e')
        False -> modifyChildren (elimLHPP tenv kv tcv) a
elimLHPP tenv kv tcv e = modifyChildren (elimLHPP tenv kv tcv) e

isNestedLPP :: TCValues -> Expr -> Bool
isNestedLPP tcv (Var (Id n _)) = n == lhPP tcv 
isNestedLPP tcv (App e _) = isNestedLPP tcv e
isNestedLPP _ _ = False

isNestedLHTC :: TCValues -> Expr -> Bool
isNestedLHTC tcv (Var (Id _ (TyConApp n _))) = n == lhTC tcv 
isNestedLHTC tcv (App e _) = isNestedLHTC tcv e
isNestedLHTC _ _ = False

-- We skip checking the outermost arg, which is always the type the lhPP
-- function is walking over
isRedundantNestedArg :: KnownValues -> TCValues -> Expr -> Bool
isRedundantNestedArg kv tcv (App e _) = isRedundantNestedArg' kv tcv e
isRedundantNestedArg _ _ _ = False

isRedundantNestedArg' :: KnownValues -> TCValues -> Expr -> Bool
isRedundantNestedArg' _ tcv (Var (Id n _)) = n == lhPP tcv 
isRedundantNestedArg' kv tcv (App e e') = isRedundantNestedArg' kv tcv e && isRedundantArg kv tcv e'
isRedundantNestedArg' _ _ _ = False

isRedundantArg :: KnownValues -> TCValues -> Expr -> Bool
isRedundantArg _ _ (Type _) = True
isRedundantArg _ tcv (Var (Id _ (TyConApp n _))) = n == lhTC tcv
isRedundantArg kv _ l@(Lam _ _) = isIdentity kv l
isRedundantArg _ tcv a@(App _ _) = isNestedLHTC tcv a
isRedundantArg _ _ _ = False

isIdentity :: KnownValues -> Expr -> Bool
isIdentity kv (Lam _ (Data (DataCon n _ _))) = n == dcTrue kv
isIdentity _ _ = False

-- | elimCalls2
-- If one of the arguments to a function with name f with 2 arguments is a,
-- replaces the function call with the other arg
elimCalls2 :: Name -> Expr -> Expr -> Expr
elimCalls2 n e = modify (elimCalls2' n e)

elimCalls2' :: Name -> Expr -> Expr -> Expr
elimCalls2' f a e
    | App (App (Var f') r) a' <- e
    , f == idName f'
    , a == a' = r
    |  App (App (Var f') a') r <- e
    , f == idName f'
    , a == a' = r 
    | otherwise = e



eCheck = (Assume 
            (App 
              (Var (Id (Name "f" (Just "GHC.Classes") 8214565720323801952 (Just (Span {start = Loc {line = 369, col = 7, file = "../base-4.9.1.0/GHC/Classes2.hs"}, end = Loc {line = 369, col = 9, file = "../base-4.9.1.0/GHC/Classes2.hs"}}))) (TyFun (TyConApp (Name "Bool" (Just "GHC.Types") 0 Nothing) []) (TyFun (TyConApp (Name "Bool" (Just "GHC.Types") 0 Nothing) []) (TyConApp (Name "Bool" (Just "GHC.Types") 0 Nothing) []))))) 
              (App 
                (App 
                  (Var (Id (Name "LHpp" Nothing 0 Nothing) TyUnknown)) 
                  (Lam 
                    (Id (Name "fs?" Nothing 112486 Nothing) (TyConApp (Name "List" (Just "List") 8214565720323847245 (Just (Span {start = Loc {line = 74, col = 1, file = "./tests/Liquid/List.lhs"}, end = Loc {line = 76, col = 39, file = "./tests/Liquid/List.lhs"}}))) [TyVar (Id (Name "v" Nothing 6989586621679020522 (Just (Span {start = Loc {line = 62, col = 14, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}, end = Loc {line = 62, col = 40, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}}))) TYPE)])) 
                      (App 
                        (Var (Id (Name "&&" (Just "GHC.Classes") 8214565720323801952 (Just (Span {start = Loc {line = 369, col = 7, file = "../base-4.9.1.0/GHC/Classes2.hs"}, end = Loc {line = 369, col = 9, file = "../base-4.9.1.0/GHC/Classes2.hs"}}))) (TyFun (TyConApp (Name "Bool" (Just "GHC.Types") 0 Nothing) []) (TyFun (TyConApp (Name "Bool" (Just "GHC.Types") 0 Nothing) []) (TyConApp (Name "Bool" (Just "GHC.Types") 0 Nothing) []))))) 
                        (App 
                          (Lam 
                            (Id (Name "lq_tmp$36$x$35$$35$694" (Just "") 0 Nothing) (TyConApp (Name "List" (Just "List") 8214565720323847245 (Just (Span {start = Loc {line = 74, col = 1, file = "./tests/Liquid/List.lhs"}, end = Loc {line = 76, col = 39, file = "./tests/Liquid/List.lhs"}}))) [TyVar (Id (Name "v" Nothing 6989586621679020522 (Just (Span {start = Loc {line = 62, col = 14, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}, end = Loc {line = 62, col = 40, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}}))) TYPE)])) 
                            (Data (DataCon (Name "True" (Just "GHC.Types") 0 Nothing) (TyConApp (Name "Bool" (Just "GHC.Types") 0 Nothing) []) []))
                          ) 
                          (Var (Id (Name "fs?" Nothing 112486 Nothing) (TyConApp (Name "List" (Just "List") 8214565720323847245 (Just (Span {start = Loc {line = 74, col = 1, file = "./tests/Liquid/List.lhs"}, end = Loc {line = 76, col = 39, file = "./tests/Liquid/List.lhs"}}))) [TyVar (Id (Name "v" Nothing 6989586621679020522 (Just (Span {start = Loc {line = 62, col = 14, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}, end = Loc {line = 62, col = 40, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}}))) TYPE)])))
                        )
                      )
                  )
                ) 
                (Var (Id (Name "ret" Nothing 0 Nothing) (TyConApp (Name "Map" (Just "Data.Map") 8214565720323826620 (Just (Span {start = Loc {line = 472, col = 1, file = "../base-4.9.1.0/Data/Map.hs"}, end = Loc {line = 472, col = 31, file = "../base-4.9.1.0/Data/Map.hs"}}))) [TyVar (Id (Name "k" Nothing 6989586621679020521 (Just (Span {start = Loc {line = 62, col = 14, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}, end = Loc {line = 62, col = 40, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}}))) TYPE),TyConApp (Name "List" (Just "List") 8214565720323847245 (Just (Span {start = Loc {line = 74, col = 1, file = "./tests/Liquid/List.lhs"}, end = Loc {line = 76, col = 39, file = "./tests/Liquid/List.lhs"}}))) [TyVar (Id (Name "v" Nothing 6989586621679020522 (Just (Span {start = Loc {line = 62, col = 14, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}, end = Loc {line = 62, col = 40, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}}))) TYPE)]])))
              )
            )

      ) (Var (Id (Name "a" Nothing 0 Nothing) TyUnknown))


eCheck2 = (Assume 
            (App 
              (Var (Id (Name "f" (Just "GHC.Classes") 8214565720323801952 (Just (Span {start = Loc {line = 369, col = 7, file = "../base-4.9.1.0/GHC/Classes2.hs"}, end = Loc {line = 369, col = 9, file = "../base-4.9.1.0/GHC/Classes2.hs"}}))) (TyFun (TyConApp (Name "Bool" (Just "GHC.Types") 0 Nothing) []) (TyFun (TyConApp (Name "Bool" (Just "GHC.Types") 0 Nothing) []) (TyConApp (Name "Bool" (Just "GHC.Types") 0 Nothing) []))))) 
              (App 
                (App 
                  (Var (Id (Name "LHpp" Nothing 0 Nothing) TyUnknown)) 
                  (Lam 
                    (Id (Name "fs?" Nothing 112486 Nothing) (TyConApp (Name "List" (Just "List") 8214565720323847245 (Just (Span {start = Loc {line = 74, col = 1, file = "./tests/Liquid/List.lhs"}, end = Loc {line = 76, col = 39, file = "./tests/Liquid/List.lhs"}}))) [TyVar (Id (Name "v" Nothing 6989586621679020522 (Just (Span {start = Loc {line = 62, col = 14, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}, end = Loc {line = 62, col = 40, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}}))) TYPE)])) 
                      (App 
                        (Var (Id (Name "&&" (Just "GHC.Classes") 8214565720323801952 (Just (Span {start = Loc {line = 369, col = 7, file = "../base-4.9.1.0/GHC/Classes2.hs"}, end = Loc {line = 369, col = 9, file = "../base-4.9.1.0/GHC/Classes2.hs"}}))) (TyFun (TyConApp (Name "Bool" (Just "GHC.Types") 0 Nothing) []) (TyFun (TyConApp (Name "Bool" (Just "GHC.Types") 0 Nothing) []) (TyConApp (Name "Bool" (Just "GHC.Types") 0 Nothing) []))))) 
                        (App 
                          (Lam 
                            (Id (Name "lq_tmp$36$x$35$$35$694" (Just "") 0 Nothing) (TyConApp (Name "List" (Just "List") 8214565720323847245 (Just (Span {start = Loc {line = 74, col = 1, file = "./tests/Liquid/List.lhs"}, end = Loc {line = 76, col = 39, file = "./tests/Liquid/List.lhs"}}))) [TyVar (Id (Name "v" Nothing 6989586621679020522 (Just (Span {start = Loc {line = 62, col = 14, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}, end = Loc {line = 62, col = 40, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}}))) TYPE)])) 
                            (Data (DataCon (Name "True" (Just "GHC.Types") 0 Nothing) (TyConApp (Name "Bool" (Just "GHC.Types") 0 Nothing) []) []))
                          ) 
                          (Var (Id (Name "fs?" Nothing 112486 Nothing) (TyConApp (Name "List" (Just "List") 8214565720323847245 (Just (Span {start = Loc {line = 74, col = 1, file = "./tests/Liquid/List.lhs"}, end = Loc {line = 76, col = 39, file = "./tests/Liquid/List.lhs"}}))) [TyVar (Id (Name "v" Nothing 6989586621679020522 (Just (Span {start = Loc {line = 62, col = 14, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}, end = Loc {line = 62, col = 40, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}}))) TYPE)])))
                        )
                      )
                  )
                ) 
                (Var (Id (Name "ret" Nothing 0 Nothing) (TyConApp (Name "Map" (Just "Data.Map") 8214565720323826620 (Just (Span {start = Loc {line = 472, col = 1, file = "../base-4.9.1.0/Data/Map.hs"}, end = Loc {line = 472, col = 31, file = "../base-4.9.1.0/Data/Map.hs"}}))) [TyVar (Id (Name "k" Nothing 6989586621679020521 (Just (Span {start = Loc {line = 62, col = 14, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}, end = Loc {line = 62, col = 40, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}}))) TYPE),TyConApp (Name "List" (Just "List") 8214565720323847245 (Just (Span {start = Loc {line = 74, col = 1, file = "./tests/Liquid/List.lhs"}, end = Loc {line = 76, col = 39, file = "./tests/Liquid/List.lhs"}}))) [TyVar (Id (Name "v" Nothing 6989586621679020522 (Just (Span {start = Loc {line = 62, col = 14, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}, end = Loc {line = 62, col = 40, file = "/Users/BillHallahan/Documents/Research/SymbolicExecution/G2/tests/Liquid/MapReduceInfer/MapReduce.lhs"}}))) TYPE)]])))
              )
            )

      ) (Var (Id (Name "a" Nothing 0 Nothing) TyUnknown))
