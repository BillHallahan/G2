module G2.Internals.Initialization.Interface where

import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support
import G2.Internals.Initialization.DeepSeqWalks
import G2.Internals.Initialization.ElimTicks
import G2.Internals.Initialization.ElimTypeSynonyms
import G2.Internals.Initialization.Functionalizer
import G2.Internals.Initialization.InitVarLocs

runInitialization :: ExprEnv -> TypeEnv -> NameGen -> [Type] -> [Name] ->
    (ExprEnv, TypeEnv, NameGen, FuncInterps, ApplyTypes, Walkers)
runInitialization eenv tenv ng ts tgtNames =
    let
        eenv2 = elimTypeSyms tenv eenv
        tenv2 = elimTypeSymsTEnv tenv
        (eenv3, ng2, ds_walkers) = createDeepSeqWalks eenv2 tenv2 ng
        (tenv3, eenv4, ft, at, ng3) = functionalize tenv2 eenv3 ng2 ts tgtNames
    in
    (elimTicks $ initVarLocs $ eenv4, tenv3, ng3, ft, at, ds_walkers)
