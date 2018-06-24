module G2.Internals.Initialization.Interface where

import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support hiding (State (..))
import G2.Internals.Language.TypeClasses
import G2.Internals.Initialization.DeepSeqWalks
import G2.Internals.Initialization.ElimTicks
import G2.Internals.Initialization.ElimTypeSynonyms
import G2.Internals.Initialization.Functionalizer
import G2.Internals.Initialization.InitVarLocs
import G2.Internals.Initialization.StructuralEq
import G2.Internals.Initialization.Types

runInitialization :: ExprEnv -> TypeEnv -> NameGen -> KnownValues -> TypeClasses -> [Type] -> [Name] ->
    (SimpleState, FuncInterps, ApplyTypes, Walkers)
runInitialization eenv tenv ng kv tc ts tgtNames =
    let
        eenv2 = elimTypeSyms tenv eenv
        tenv2 = elimTypeSymsTEnv tenv
        (eenv3, ng2, ds_walkers) = createDeepSeqWalks eenv2 tenv2 ng

        s = SimpleState { expr_env = eenv3
                        , type_env = tenv2
                        , name_gen = ng2
                        , known_values = kv
                        , type_classes = tc }

        s' = execSimpleStateM (createStructEqFuncs ts) s
        ((ft, at), s'') = runSimpleStateM (functionalize ts tgtNames) s'
        s''' = elimTicks . initVarLocs $ s''
    in
    (s''', ft, at, ds_walkers)
