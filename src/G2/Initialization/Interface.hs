{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module G2.Initialization.Interface (MkArgTypes, runInitialization1, runInitialization2) where

import G2.Config
import G2.Initialization.TrivializeDCs
import qualified G2.Language.ExprEnv as E
import G2.Language.Expr
import G2.Language.KnownValues
import G2.Language.Syntax
import G2.Language.Support hiding (State (..))
import G2.Language.Typing
import G2.Initialization.ElimTicks
import G2.Initialization.ElimTypeSynonyms
import G2.Initialization.FpToRational
import G2.Initialization.Handles
import G2.Initialization.InitVarLocs
import G2.Initialization.Types as IT
import qualified G2.Language.TyVarEnv as TV
import G2.Translation.GHC (ImportDeclQualifiedStyle(NotQualified))

type MkArgTypes = IT.SimpleState -> [Type]

runInitialization1 :: IT.SimpleState -> IT.SimpleState
runInitialization1 s =
    let
        s'@(IT.SimpleState { expr_env = eenv, IT.type_env = tenv, IT.type_classes = tc }) = elimBreakpoints . initVarLocs $ s
        eenv2 = elimTypeSyms tenv eenv
        tenv2 = elimTypeSymsTEnv tenv
        tc2 = elimTypeSyms tenv tc
    in
    s' { IT.expr_env = eenv2, IT.type_env = tenv2, IT.type_classes = tc2}

runInitialization2 :: Config -> IT.SimpleState -> MkArgTypes -> IT.SimpleState
runInitialization2 config s@(IT.SimpleState { IT.expr_env = eenv
                                            , IT.name_gen = ng
                                            , IT.known_values = kv }) argTys =
    let
        ts = argTys s

        (eenv3, hs, ng2) = mkHandles eenv kv ng

        eenv4 = if error_asserts config then assertFalseOnError kv eenv3 else eenv3

        t = Id (Name "t" Nothing 0 Nothing) TYPE
        str = Id (Name "s" Nothing 0 Nothing) (tyString kv)
        x = Id (Name "x" Nothing 0 Nothing) TyLitInt

        smt_con = smt_config config
        (eenv5, ng3) = if smt_strings smt_con == NoSMTStrings
                                then (E.insert (typeIndex kv) 
                                            (Lam TypeL t . Lam TermL x . Lit $ LitInt 0) eenv4, ng2)
                                else trivializeDCs TV.empty ng2 kv eenv4
        eenv6 = if smt_strings smt_con == NoSMTStrings
                        then E.insert (adjStr kv) 
                                      (Lam TypeL t . Lam TermL x . Lam TermL str $ Var x) eenv5
                        else eenv5
        eenv7 = if quantified_smt_strings smt_con == NoQuantifiers
                        then E.insert (strQuantifiers kv) 
                                      (Lam TermL x $ Lit (LitInt 0)) eenv6
                        else eenv6

        s' = s { IT.expr_env = eenv7
               , IT.name_gen = ng3
               , IT.handles = hs}
        
        s'' = if fp_handling (symex_heuristics config) == RationalFP then substRational s' else s'
    in
    s''

-- | Wraps all error primitives in `Assert False`.
assertFalseOnError :: ASTContainer m Expr => KnownValues -> m -> m
assertFalseOnError kv = modifyContainedASTs (assertFalseOnError' kv)

assertFalseOnError' :: KnownValues -> Expr -> Expr
assertFalseOnError' kv err@(Prim Error _) = Assert Nothing (mkFalse kv) err
assertFalseOnError' kv e = modifyChildren (assertFalseOnError' kv) e