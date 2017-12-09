module G2.Internals.Initialization.Interface where

import Debug.Trace as T

import G2.Internals.Language.Naming
import G2.Internals.Language.Support
import G2.Internals.Initialization.InjectSpecials
import G2.Internals.Initialization.CreateFuncs
import G2.Internals.Initialization.Functionalizer
import G2.Internals.Initialization.TyBinderInit

runInitialization :: ExprEnv -> TypeEnv -> NameGen -> 
    (ExprEnv, TypeEnv, NameGen, FuncInterps, ApplyTypes, Walkers, Walkers, Wrappers)
runInitialization eenv tenv ng =
    let
        tenv1 = injectSpecials tenv eenv
        (tenv2, ng2) = tyBinderInit tenv1 ng
        (eenv2, ng3, ds_walkers) = createDeepSeqWalks eenv tenv2 ng2
        (eenv3, ng4, pt_walkers) = createPolyPredWalks eenv2 tenv2 ng3
        (eenv4, ng5, wrap) = createHigherOrderWrappers eenv3 tenv2 ng4
        (tenv3, eenv5, ft, at, ng6) = functionalize tenv2 eenv4 ng5
    in
    (eenv5, tenv3, ng6, ft, at, ds_walkers, pt_walkers, wrap)
