module G2.Internals.Initialization.Interface where

import G2.Internals.Language.Naming
import G2.Internals.Language.Support
import G2.Internals.Initialization.CreateFuncs
import G2.Internals.Initialization.Functionalizer
import G2.Internals.Initialization.TyBinderInit

runInitialization :: ExprEnv -> TypeEnv -> NameGen -> 
    (ExprEnv, TypeEnv, NameGen, FuncInterps, ApplyTypes, Walkers, Walkers, Wrappers)
runInitialization eenv tenv ng =
    let
        (tenv2, eenv2, ft, at, ng2) = functionalize tenv eenv ng
        (tenv3, ng3) = tyBinderInit tenv2 ng2
        (eenv3, ng4, ds_walkers) = createDeepSeqWalks eenv2 tenv3 ng3
        (eenv4, ng5, pt_walkers) = createPolyPredWalks eenv3 tenv3 ng4
        (eenv5, ng6, wrap) = createHigherOrderWrappers eenv4 tenv3 ng5
    in
    (eenv5, tenv3, ng6, ft, at, ds_walkers, pt_walkers, wrap)