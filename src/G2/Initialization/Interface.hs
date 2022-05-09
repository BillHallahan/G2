module G2.Initialization.Interface where

import G2.Language.Syntax
import G2.Language.Support hiding (State (..))
import G2.Initialization.DeepSeqWalks
import G2.Initialization.ElimTicks
import G2.Initialization.ElimTypeSynonyms
import G2.Initialization.InitVarLocs
import G2.Initialization.StructuralEq
import G2.Initialization.Types as IT

type MkArgTypes = IT.SimpleState -> [Type]

runInitialization1 :: IT.SimpleState -> IT.SimpleState
runInitialization1 = elimTicks . initVarLocs

runInitialization2 :: IT.SimpleState -> MkArgTypes -> (IT.SimpleState, Walkers)
runInitialization2 s@(IT.SimpleState { IT.expr_env = eenv
                                     , IT.type_env = tenv
                                     , IT.name_gen = ng
                                     , IT.type_classes = tc }) argTys =
    let
        eenv2 = elimTypeSyms tenv eenv
        tenv2 = elimTypeSymsTEnv tenv
        tc2 = elimTypeSyms tenv tc
        (eenv3, ng2, ds_walkers) = createDeepSeqWalks eenv2 tenv2 ng

        ts = argTys (s { IT.expr_env = eenv3, IT.type_env = tenv2, IT.type_classes = tc2 })

        s' = s { IT.expr_env = eenv3
               , IT.type_env = tenv2
               , IT.name_gen = ng2
               , IT.type_classes = tc2 }

        s'' = execSimpleStateM (createStructEqFuncs ts) s'
    in
    (s'', ds_walkers)