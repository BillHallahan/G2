module G2.Internals.Initialization.Interface where

import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support
import G2.Internals.Initialization.DeepSeqWalks
import G2.Internals.Initialization.ElimTypeSynonyms
import G2.Internals.Initialization.Functionalizer

runInitialization :: ExprEnv -> TypeEnv -> NameGen -> [Type] -> [Name] ->
    (ExprEnv, TypeEnv, NameGen, FuncInterps, ApplyTypes, Walkers)
runInitialization eenv tenv ng ts tgtNames =
    let
        eenv2 = elimTypeSyms tenv eenv
        tenv2 = elimTypeSymsTEnv tenv
        (eenv3, ng2, ds_walkers) = createDeepSeqWalks eenv2 tenv2 ng
        (eenv4, ng4) = (eenv3, ng2)
        (tenv3, eenv5, ft, at, ng5) = functionalize tenv2 eenv4 ng4 ts tgtNames
    in
    (eenv5, tenv3, ng5, ft, at, ds_walkers)
