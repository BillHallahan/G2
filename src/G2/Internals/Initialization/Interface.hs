module G2.Internals.Initialization.Interface where

import G2.Internals.Language.Naming
import G2.Internals.Language.Support
import G2.Internals.Initialization.DeepSeqWalks
import G2.Internals.Initialization.Functionalizer
import G2.Internals.Initialization.KnownValues

runInitialization :: ExprEnv -> TypeEnv -> NameGen -> 
    (ExprEnv, TypeEnv, NameGen, FuncInterps, ApplyTypes, Walkers, KnownValues)
runInitialization eenv tenv ng =
    let
        -- tenv2 = injectSpecials tenv eenv
        
        kv = initKnownValues eenv tenv

        (eenv2, ng2, ds_walkers) = createDeepSeqWalks eenv tenv ng
        -- (eenv3, ng3, pt_walkers) = createPolyPredWalks eenv2 tenv ng2 kv
        -- (eenv4, ng4, wrap) = createHigherOrderWrappers eenv3 tenv ng3 kv
        (eenv4, ng4) = (eenv2, ng2)
        (tenv2, eenv5, ft, at, ng5) = functionalize tenv eenv4 ng4
    in
    (eenv5, tenv2, ng5, ft, at, ds_walkers, kv)
