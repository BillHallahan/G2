module G2.Internals.Initialization.Interface where

import G2.Internals.Language.Naming
import G2.Internals.Language.Support
import G2.Internals.Initialization.CreateWalks
import G2.Internals.Initialization.Defunctionalizor
import G2.Internals.Initialization.FreeBind
import G2.Internals.Initialization.Functionalizer
import G2.Internals.Initialization.LetFloating

runInitialization :: ExprEnv -> TypeEnv -> NameGen -> (ExprEnv, TypeEnv, NameGen, FuncInterps, Walkers)
runInitialization eenv tenv ng =
    let
        eenv2 = freeVarsBind eenv
        (eenv3, ng2) = letFloat eenv2 ng
        (eenv4, tenv2, ng3, ft) = defunctionalize eenv3 tenv ng2
        (eenv5, walkers, ng4) = createWalks eenv4 tenv2 ng3
    in
    (eenv5, tenv2, ng4, ft, walkers)