module G2.Internals.Initialization.Interface where

import Debug.Trace as T

import G2.Internals.Language.Naming
import G2.Internals.Language.Support
import G2.Internals.Initialization.InjectSpecials
import G2.Internals.Initialization.CreateFuncs
import G2.Internals.Initialization.Functionalizer

runInitialization :: ExprEnv -> TypeEnv -> NameGen -> 
    (ExprEnv, TypeEnv, NameGen, FuncInterps, ApplyTypes, Walkers, Walkers, Wrappers)
runInitialization eenv tenv ng =
    let
        tenv2 = injectSpecials tenv eenv
        (eenv2, ng2, ds_walkers) = createDeepSeqWalks eenv tenv2 ng
        (eenv3, ng3, pt_walkers) = createPolyPredWalks eenv2 tenv2 ng2
        (eenv4, ng4, wrap) = createHigherOrderWrappers eenv3 tenv2 ng3
        (tenv3, eenv5, ft, at, ng5) = functionalize tenv2 eenv4 ng4
    in
    (eenv5, tenv3, ng5, ft, at, ds_walkers, pt_walkers, wrap)
