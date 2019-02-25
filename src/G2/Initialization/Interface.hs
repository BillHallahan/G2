module G2.Initialization.Interface where

import G2.Language.Syntax
import G2.Language.Support hiding (State (..))
import G2.Language.Naming
import G2.Initialization.DeepSeqWalks
import G2.Initialization.ElimTicks
import G2.Initialization.ElimTypeSynonyms
import G2.Initialization.Functionalizer
import G2.Initialization.InitVarLocs
import G2.Initialization.StructuralEq
import G2.Initialization.Types

import Data.HashSet

runInitialization :: SimpleState -> [Type] -> HashSet Name -> NameGen ->
    (SimpleState, FuncInterps, ApplyTypes, Walkers, NameGen)
runInitialization s@(SimpleState { expr_env = eenv
                                 , type_env = tenv
                                 , type_classes = tc }) ts tgtNames ng =
    let
        eenv2 = elimTypeSyms tenv eenv
        tenv2 = elimTypeSymsTEnv tenv
        tc2 = elimTypeSyms tenv tc
        (eenv3, ng2, ds_walkers) = createDeepSeqWalks eenv2 tenv2 ng

        s' = s { expr_env = eenv3
               , type_env = tenv2
               , type_classes = tc2 }

        s'' = execSimpleStateM (createStructEqFuncs ts) s'
        ((ft, at), s''') = runSimpleStateM (functionalize ts tgtNames) s''
        s'''' = elimTicks . initVarLocs $ s'''
    in
    (s'''', ft, at, ds_walkers, ng2)
