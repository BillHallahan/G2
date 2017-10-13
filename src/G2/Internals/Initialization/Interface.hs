module G2.Internals.Initialization.Interface where

import G2.Internals.Language.Naming
import G2.Internals.Language.Support
import G2.Internals.Initialization.CreateWalks
import G2.Internals.Initialization.Functionalizer

runInitialization :: ExprEnv -> TypeEnv -> NameGen -> (ExprEnv, TypeEnv, NameGen, FuncInterps, ApplyTypes, Walkers)
runInitialization eenv tenv ng =
    let
        (tenv2, eenv2, ft, at, ng2) = functionalize tenv eenv ng
        (eenv3, walkers, ng3) = createWalks eenv2 tenv2 ng2
    in
    (eenv3, tenv2, ng3, ft, at, walkers)