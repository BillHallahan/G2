{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

module G2.Liquid.Interface where

import G2.Config.Config

import G2.Translation
import G2.Interface
import G2.Language as Lang
import qualified G2.Language.ExprEnv as E

import G2.Execution

import G2.Initialization.MkCurrExpr

import G2.Liquid.AddCFBranch
import G2.Liquid.AddLHTC
import G2.Liquid.AddOrdToNum
import G2.Liquid.Conversion
import G2.Liquid.ConvertCurrExpr
import G2.Liquid.Helpers
import G2.Liquid.LHReducers
import G2.Liquid.Measures
import G2.Liquid.Simplify
import G2.Liquid.SpecialAsserts
import G2.Liquid.TCGen
import G2.Liquid.Types
import G2.Solver hiding (solve)

import G2.Lib.Printers

import Language.Haskell.Liquid.Types hiding (Config, cls, names)
import qualified Language.Haskell.Liquid.Types.PrettyPrint as PPR
import Language.Haskell.Liquid.UX.CmdLine

import qualified Language.Fixpoint.Types.PrettyPrint as FPP

import Control.Exception
import Data.List
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.IO as TI

import Var

import G2.Language.KnownValues

data LHReturn = LHReturn { calledFunc :: FuncInfo
                         , violating :: Maybe FuncInfo
                         , abstracted :: [FuncInfo] } deriving (Eq, Show)

data FuncInfo = FuncInfo { func :: T.Text
                         , funcArgs :: T.Text
                         , funcReturn :: T.Text } deriving (Eq, Show)

-- | findCounterExamples
-- Given (several) LH sources, and a string specifying a function name,
-- attempt to find counterexamples to the functions liquid type
findCounterExamples :: [FilePath] -> [FilePath] -> T.Text -> [FilePath] -> [FilePath] -> Config -> IO (([ExecRes [FuncCall]], Bindings), Lang.Id)
findCounterExamples proj fp entry libs lhlibs config = do
    let config' = config { mode = Liquid }

    lh_config <- getOpts []

    ghci <- try $ getGHCInfos lh_config proj fp lhlibs :: IO (Either SomeException [GhcInfo])
    
    let ghci' = case ghci of
                  Right g_c -> g_c
                  Left e -> error $ "ERROR OCCURRED IN LIQUIDHASKELL\n" ++ show e

    tgt_trans <- translateLoaded proj fp libs (simplTranslationConfig { simpl = False }) config'

    runLHCore entry tgt_trans ghci' config'

runLHCore :: T.Text -> (Maybe T.Text, ExtractedG2)
                    -> [GhcInfo]
                    -> Config
                    -> IO (([ExecRes [FuncCall]], Bindings), Lang.Id)
runLHCore entry (mb_modname, exg2) ghci config = do
    (ifi, cfn, final_st, bindings, pres_names) <- liquidState entry (mb_modname, exg2) ghci config
    let annm = annotations $ track final_st

    SomeSolver solver <- initSolver config
    let simplifier = ADTSimplifier arbValue

    -- We replace certain function name lists in the final State with names
    -- mapping into the measures from the LHState.  These functions do not
    -- need to be passed the LH typeclass, so this ensures use of Names from
    -- these lists will work, without us having to modify all of G2 to account
    -- for the LH typeclass.

    let tr_ng = mkNameGen ()
    let state_name = Name "state" Nothing 0 Nothing

    let (limHalt, limOrd) = limitByAccepted (cut_off config)

    let share = sharing config

    (ret, final_bindings) <- if higherOrderSolver config == AllFuncs
              then runG2WithSomes
                    (SomeReducer NonRedPCRed
                      <~| (case logStates config of
                            Just fp -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn :<~ Logger fp)
                            Nothing -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn)))
                    (SomeHalter
                      (MaxOutputsHalter (maxOutputs config)
                        :<~> ZeroHalter (steps config)
                        :<~> LHAbsHalter entry mb_modname (expr_env final_st)
                        :<~> limHalt
                        :<~> SwitchEveryNHalter (switch_after config)
                        :<~> AcceptHalter))
                    (SomeOrderer limOrd)
                    solver simplifier (pres_names ++ names annm) final_st bindings
              else runG2WithSomes
                    (SomeReducer (NonRedPCRed :<~| TaggerRed state_name tr_ng)
                      <~| (case logStates config of
                            Just fp -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn :<~ Logger fp)
                            Nothing -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn)))
                    (SomeHalter
                      (DiscardIfAcceptedTag state_name
                        :<~> MaxOutputsHalter (maxOutputs config)
                        :<~> ZeroHalter (steps config)
                        :<~> LHAbsHalter entry mb_modname (expr_env final_st)
                        :<~> limHalt
                        :<~> SwitchEveryNHalter (switch_after config)
                        :<~> AcceptHalter))
                    (SomeOrderer limOrd)
                    solver simplifier (pres_names ++ names annm) final_st bindings
    
    -- We filter the returned states to only those with the minimal number of abstracted functions
    let mi = case length ret of
                  0 -> 0
                  _ -> minimum $ map (\(ExecRes {final_state = s}) -> length $ abstract_calls $ track s) ret
    let ret' = filter (\(ExecRes {final_state = s}) -> mi == (length $ abstract_calls $ track s)) ret

    let exec_res = 
                map (\(ExecRes { final_state = s
                               , conc_args = es
                               , conc_out = e
                               , violated = ais}) ->
                      (ExecRes { final_state =
                                    s {track = map (subVarFuncCall (model s) (expr_env s) (type_classes s)) $ abstract_calls $ track s}
                               , conc_args = es
                               , conc_out = e
                               , violated = ais})) ret'

    -- mapM_ (\er -> do
    --     print . track $ final_state er 
    --     putStrLn . flip pprExecStateStr bindings''' . final_state $ er) exec_res
    -- mapM (\(_, es, e, ais) -> do print es; print e; print ais) states

    close solver

    return ((exec_res, final_bindings), ifi)

liquidState :: T.Text -> (Maybe T.Text, ExtractedG2)
                      -> [GhcInfo]
                      -> Config
                      -> IO (Lang.Id, CounterfactualName, State LHTracker, Bindings, [Name])
liquidState entry (mb_modname, exg2) ghci config = do
    let (init_state, ifi, bindings) = initState exg2 True entry mb_modname (mkCurrExpr Nothing Nothing) config
    let (init_state', bindings') = (markAndSweepPreserving (reqNames init_state) init_state bindings)
    let cleaned_state = init_state' { type_env = type_env init_state } 

    let (no_part_state@(State {expr_env = np_eenv})) = cleaned_state
    let np_ng = name_gen bindings'

    let renme = E.keys np_eenv -- \\ nub (Lang.names (type_classes no_part_state))
    let ((meenv, mkv, mtc, minst), ng') = doRenames renme np_ng 
            (np_eenv, known_values no_part_state, type_classes no_part_state, higher_order_inst bindings')
    
    let ng_bindings = bindings' {name_gen = ng'}

    let ng_state = no_part_state {track = []}

    let (lh_state, lh_bindings) = createLHState meenv mkv ng_state ng_bindings

    let (cfn, (merged_state, bindings'')) = runLHStateM (initializeLH (counterfactual config) ghci ifi lh_bindings) lh_state lh_bindings
    let bindings''' = bindings'' { higher_order_inst = minst }

    let tcv = tcvalues merged_state
    let merged_state' = deconsLHState merged_state

    let pres_names = reqNames merged_state' ++ names tcv ++ names mkv

    let annm = annots merged_state

    let track_state = merged_state' {track = LHTracker { abstract_calls = []
                                                       , last_var = Nothing
                                                       , annotations = annm} }

    -- We replace certain function name lists in the final State with names
    -- mapping into the measures from the LHState.  These functions do not
    -- need to be passed the LH typeclass, so this ensures use of Names from
    -- these lists will work, without us having to modify all of G2 to account
    -- for the LH typeclass.
    let final_st = track_state { known_values = mkv
                               , type_classes = unionTypeClasses mtc (type_classes track_state)}

    return (ifi, cfn, final_st, bindings''', pres_names)

initializeLH :: Counterfactual -> [GhcInfo] -> Lang.Id -> Bindings -> LHStateM Lang.Name
initializeLH counter ghcInfos ifi bindings = do
    addLHTC
    addOrdToNum

    let lh_measures = measureSpecs ghcInfos
    createMeasures lh_measures

    let specs = funcSpecs ghcInfos
    mergeLHSpecState specs

    addSpecialAsserts
    addTrueAsserts ifi

    -- The simplification works less well on some of the Core generated by convertCurrExpr,
    -- so we apply the simplification first
    simplify

    ns <- convertCurrExpr ifi bindings

    cfn <- if counter == Counterfactual
                then addCounterfactualBranch ns
                else return (Name "" Nothing 0 Nothing)

    return cfn

reqNames :: State t -> [Name]
reqNames (State { expr_env = eenv
                , type_classes = tc
                , known_values = kv}) = 
    Lang.names [ mkGe eenv
               , mkGt eenv
               , mkEq eenv
               , mkNeq eenv
               , mkLt eenv
               , mkLe eenv
               , mkAnd eenv
               , mkOr eenv
               , mkNot eenv
               , mkPlus eenv
               , mkMinus eenv
               , mkMult eenv
               -- , mkDiv eenv
               , mkMod eenv
               , mkNegate eenv
               , mkImplies eenv
               , mkIff eenv
               , mkFromInteger eenv
               -- , mkToInteger eenv
               ]
    ++
    Lang.names 
      (M.filterWithKey 
          (\k _ -> k == eqTC kv || k == numTC kv || k == ordTC kv || k == integralTC kv || k == structEqTC kv) 
          (toMap tc)
      )

pprint :: (Var, LocSpecType) -> IO ()
pprint (v, r) = do
    let i = mkIdUnsafe v

    let doc = PPR.rtypeDoc FPP.Full $ val r
    putStrLn $ show i
    putStrLn $ show doc

printLHOut :: Lang.Id -> [ExecRes [FuncCall]] -> IO ()
printLHOut entry = printParsedLHOut . parseLHOut entry

printParsedLHOut :: [LHReturn] -> IO ()
printParsedLHOut [] = return ()
printParsedLHOut (LHReturn { calledFunc = FuncInfo {func = f, funcArgs = call, funcReturn = output}
                           , violating = Nothing
                           , abstracted = abstr} : xs) = do
    putStrLn "The call"
    TI.putStrLn $ call `T.append` " = " `T.append` output
    TI.putStrLn $ "violates " `T.append` f `T.append` "'s refinement type"
    printAbs abstr
    putStrLn ""
    printParsedLHOut xs
printParsedLHOut (LHReturn { calledFunc = FuncInfo {funcArgs = call, funcReturn = output}
                           , violating = Just (FuncInfo {func = f, funcArgs = call', funcReturn = output'})
                           , abstracted = abstr } : xs) = do
    TI.putStrLn $ call `T.append` " = " `T.append` output
    putStrLn "makes a call to"
    TI.putStrLn $ call' `T.append` " = " `T.append` output'
    TI.putStrLn $ "violating " `T.append` f `T.append` "'s refinement type"
    printAbs abstr
    putStrLn ""
    printParsedLHOut xs

printAbs :: [FuncInfo] -> IO ()
printAbs fi = do
    let fn = T.intercalate ", " $ map func fi

    if length fi > 0 then do
        putStrLn "if"
        mapM_ printFuncInfo fi
        if length fi > 1 then do
            TI.putStrLn $ "Strengthen the refinement types of " `T.append`
                          fn `T.append` " to eliminate these possibilities"
            putStrLn "Abstract"
        else do
            TI.putStrLn $ "Strengthen the refinement type of " `T.append`
                          fn `T.append` " to eliminate this possibility"
            putStrLn "Abstract"
    else
        putStrLn "Concrete"

printFuncInfo :: FuncInfo -> IO ()
printFuncInfo (FuncInfo {funcArgs = call, funcReturn = output}) =
    TI.putStrLn $ call `T.append` " = " `T.append` output

parseLHOut :: Lang.Id -> [ExecRes [FuncCall]] -> [LHReturn]
parseLHOut _ [] = []
parseLHOut entry ((ExecRes { final_state = s
                           , conc_args = inArg
                           , conc_out = ex
                           , violated = ais}):xs) =
  let 
      tl = parseLHOut entry xs
      funcCall = T.pack $ mkCleanExprHaskell s 
               . foldl (\a a' -> App a a') (Var entry) $ inArg
      funcOut = T.pack $ mkCleanExprHaskell s $ ex

      called = FuncInfo {func = nameOcc $ idName entry, funcArgs = funcCall, funcReturn = funcOut}
      viFunc = fmap (parseLHFuncTuple s) ais

      abstr = map (parseLHFuncTuple s) $ track s
  in
  LHReturn { calledFunc = called
           , violating = if called `sameFuncNameArgs` viFunc then Nothing else viFunc
           , abstracted = abstr} : tl

lhStateToCE :: Lang.Id -> ExecRes [FuncCall] -> CounterExample
lhStateToCE i (ExecRes { final_state = s
                       , conc_args = inArg
                       , conc_out = ex
                       , violated = vi})
    | Nothing <- vi' = DirectCounter initCall (track s)
    | Just c <- vi' = CallsCounter initCall c (track s)
    where
        initCall = FuncCall (idName i) inArg ex
        vi' = if initCall `sameFuncCall` vi then Nothing else vi

sameFuncCall :: FuncCall -> Maybe FuncCall -> Bool
sameFuncCall _ Nothing = False
sameFuncCall (FuncCall {funcName = f1, arguments = fa1}) 
             (Just (FuncCall {funcName = f2, arguments = fa2})) = f1 == f2 && fa1 == fa2

sameFuncNameArgs :: FuncInfo -> Maybe FuncInfo -> Bool
sameFuncNameArgs _ Nothing = False
sameFuncNameArgs (FuncInfo {func = f1, funcArgs = fa1}) (Just (FuncInfo {func = f2, funcArgs = fa2})) = f1 == f2 && fa1 == fa2

parseLHFuncTuple :: State t -> FuncCall -> FuncInfo
parseLHFuncTuple s (FuncCall {funcName = n, arguments = ars, returns = out}) =
    let
        t = case fmap typeOf $ E.lookup n (expr_env s) of
                  Just t' -> t'
                  Nothing -> error $ "Unknown type for abstracted function " ++ show n
    in
    FuncInfo { func = nameOcc n
             , funcArgs = T.pack $ mkCleanExprHaskell s (foldl' App (Var (Id n t)) ars)
             , funcReturn = T.pack $ mkCleanExprHaskell s out }
