module G2.Internals.Initialization.Interface where

import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support
import G2.Internals.Initialization.DeepSeqWalks
import G2.Internals.Initialization.ElimTypeSynonyms
import G2.Internals.Initialization.Functionalizer
import G2.Internals.Initialization.KnownValues

runInitialization :: ExprEnv -> TypeEnv -> NameGen -> [Type] -> [Name] ->
    (ExprEnv, TypeEnv, NameGen, FuncInterps, ApplyTypes, Walkers)
runInitialization eenv tenv ng ts tgtNames =
    let
        -- tenv2 = injectSpecials tenv eenv
        eenv2 = elimTypeSyms tenv eenv
        tenv2 = elimTypeSymsTEnv tenv
        (eenv3, ng2, ds_walkers) = createDeepSeqWalks eenv2 tenv2 ng
        -- (eenv3, ng3, pt_walkers) = createPolyPredWalks eenv2 tenv ng2 kv
        -- (eenv4, ng4, wrap) = createHigherOrderWrappers eenv3 tenv ng3 kv
        (eenv4, ng4) = (eenv3, ng2)
        (tenv3, eenv5, ft, at, ng5) = functionalize tenv2 eenv4 ng4 ts tgtNames
    in
    (eenv5, tenv3, ng5, ft, at, ds_walkers)
