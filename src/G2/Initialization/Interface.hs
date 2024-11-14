module G2.Initialization.Interface where

import G2.Config
import G2.Language.Syntax
import G2.Language.Support hiding (State (..))
import G2.Initialization.ElimTicks
import G2.Initialization.ElimTypeSynonyms
import G2.Initialization.FpToRational
import G2.Initialization.Handles
import G2.Initialization.InitVarLocs
import G2.Initialization.Types as IT

type MkArgTypes = IT.SimpleState -> [Type]

runInitialization1 :: IT.SimpleState -> IT.SimpleState
runInitialization1 = elimBreakpoints . initVarLocs

runInitialization2 :: Config -> IT.SimpleState -> MkArgTypes -> IT.SimpleState
runInitialization2 config s@(IT.SimpleState { IT.expr_env = eenv
                                            , IT.type_env = tenv
                                            , IT.name_gen = ng
                                            , IT.known_values = kv
                                            , IT.type_classes = tc }) argTys =
    let
        eenv2 = elimTypeSyms tenv eenv
        tenv2 = elimTypeSymsTEnv tenv
        tc2 = elimTypeSyms tenv tc

        ts = argTys (s { IT.expr_env = eenv2, IT.type_env = tenv2, IT.type_classes = tc2 })

        (eenv3, hs, ng2) = mkHandles eenv2 kv ng

        s' = s { IT.expr_env = eenv3
               , IT.type_env = tenv2
               , IT.name_gen = ng2
               , IT.handles = hs
               , IT.type_classes = tc2 }
        
        s'' = if fp_handling config == RationalFP then substRational s' else s'
    in
    s''