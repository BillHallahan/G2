module G2.Internals.Initialization.Interface where

import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support hiding (State (..))
import G2.Internals.Initialization.DeepSeqWalks
import G2.Internals.Initialization.ElimTicks
import G2.Internals.Initialization.ElimTypeSynonyms
import G2.Internals.Initialization.Functionalizer
import G2.Internals.Initialization.InitVarLocs
import G2.Internals.Initialization.KnownValues
import G2.Internals.Initialization.Types

import G2.Internals.Language.Typing
import Debug.Trace

runInitialization :: ExprEnv -> TypeEnv -> NameGen -> [Type] -> [Name] ->
    (SimpleState, FuncInterps, ApplyTypes, Walkers)
runInitialization eenv tenv ng ts tgtNames =
    let
        eenv2 = elimTypeSyms tenv eenv
        tenv2 = elimTypeSymsTEnv tenv
        (eenv3, ng2, ds_walkers) = createDeepSeqWalks eenv2 tenv2 ng

        kv = initKnownValues eenv3 tenv2

        s = SimpleState { expr_env = eenv3
                        , type_env = tenv2
                        , name_gen = ng2
                        , known_values = kv }

        (s', ft, at) = functionalize s ts tgtNames
        eenv5 = elimTicks . initVarLocs $ expr_env s'

        s'' = s' { expr_env = eenv5 }
    in
    -- trace ("runInitialization ts = " ++ show ts)

    -- trace ("runInitialization ts = " ++ (show $ map (isTyFun) ts))

    -- trace ("runInitialization ts = " ++ (show $ length ts))
    (s'', ft, at, ds_walkers)
