{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Liquid.Interface where

import G2.Internals.Config.Config

import G2.Internals.Translation
import G2.Internals.Interface
import G2.Internals.Language as Lang
import qualified G2.Internals.Language.ExprEnv as E

import G2.Internals.Execution

import G2.Internals.Liquid.AddLHTC
import G2.Internals.Liquid.AddOrdToNum
import G2.Internals.Liquid.Annotations
import G2.Internals.Liquid.Conversion
import G2.Internals.Liquid.ConvertCurrExpr
import G2.Internals.Liquid.Measures
import G2.Internals.Liquid.Rules
import G2.Internals.Liquid.Simplify
import G2.Internals.Liquid.SpecialAsserts
import G2.Internals.Liquid.TCGen
import G2.Internals.Liquid.Types
import G2.Internals.Solver hiding (solve)

import G2.Lib.Printers

import Language.Haskell.Liquid.Constraint.Generate
import Language.Haskell.Liquid.Constraint.ToFixpoint
import qualified Language.Haskell.Liquid.GHC.Interface as LHI
import Language.Haskell.Liquid.Types hiding (Config, cls, names)
import qualified Language.Haskell.Liquid.Types.PrettyPrint as PPR
import Language.Haskell.Liquid.UX.CmdLine
import qualified Language.Haskell.Liquid.UX.Config as LHC

import Language.Fixpoint.Solver
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.PrettyPrint as FPP

import Control.Exception
import Data.Coerce
import Data.List
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.IO as TI

import System.Directory

import qualified GHC as GHC
import Var

import G2.Internals.Language.KnownValues

data LHReturn = LHReturn { calledFunc :: FuncInfo
                         , violating :: Maybe FuncInfo
                         , abstracted :: [FuncInfo] } deriving (Eq, Show)

data FuncInfo = FuncInfo { func :: T.Text
                         , funcArgs :: T.Text
                         , funcReturn :: T.Text } deriving (Eq, Show)

-- | findCounterExamples
-- Given (several) LH sources, and a string specifying a function name,
-- attempt to find counterexamples to the functions liquid type
findCounterExamples :: FilePath -> FilePath -> T.Text -> [FilePath] -> [FilePath] -> Config -> IO ([(State [FuncCall], [Expr], Expr, Maybe FuncCall)], Lang.Id)
findCounterExamples proj fp entry libs lhlibs config = do
    let config' = config { mode = Liquid }

    lh_config <- getOpts []

    ghc_cg <- try $ getGHCInfos lh_config proj [fp] lhlibs :: IO (Either SomeException [LHOutput])
    
    let ghc_cg' = case ghc_cg of
                  Right g_c -> g_c
                  Left e -> error $ "ERROR OCCURRED IN LIQUIDHASKELL\n" ++ show e

    tgt_trans <- translateLoaded proj fp libs False config' 

    runLHCore entry tgt_trans ghc_cg' config'

runLHCore :: T.Text -> (Maybe T.Text, Program, [ProgramType], [(Name, Lang.Id, [Lang.Id])], [Name], [Name])
                    -> [LHOutput]
                    -> Config
                    -> IO ([(State [FuncCall], [Expr], Expr, Maybe FuncCall)], Lang.Id)
runLHCore entry (mb_modname, prog, tys, cls, _, ex) ghci_cg config = do
    let (init_state, ifi) = initState prog tys cls Nothing Nothing Nothing True entry mb_modname ex config
    let cleaned_state = (markAndSweepPreserving (reqNames init_state) init_state) { type_env = type_env init_state }

    let no_part_state@(State {expr_env = np_eenv, name_gen = np_ng}) = cleaned_state

    let renme = E.keys np_eenv \\ nub (Lang.names (type_classes no_part_state))
    let ((meenv, mkv), ng') = doRenames renme np_ng (np_eenv, known_values no_part_state)
    let ng_state = no_part_state {name_gen = ng'}

    let ng_state' = ng_state {track = []}

    let lh_state = createLHState meenv mkv ng_state'

    let (abs_fun, merged_state) = runLHStateM (initializeLH ghci_cg ifi) lh_state

    let tcv = tcvalues merged_state
    let merged_state' = deconsLHState merged_state

    let pres_names = reqNames merged_state' ++ names tcv ++ names mkv

    let annm = annots merged_state
    -- print annm

    let track_state = merged_state' {track = LHTracker {abstract_calls = [], last_var = Nothing, annotations = annm} }

    SomeSMTSolver con <- getSMT config
    let con' = GroupRelated (ADTSolver :?> con)

    let final_state = track_state { known_values = mkv }


    let tr_ng = mkNameGen ()
    let state_name = Name "state" Nothing 0 Nothing

    ret <- if higherOrderSolver config == AllFuncs
              then run 
                    (NonRedPCRed config
                      :<~| LHRed abs_fun con' config) 
                    (MaxOutputsHalter 
                      :<~> ZeroHalter 
                      :<~> LHHalter entry mb_modname (expr_env init_state)) 
                    NextOrderer 
                    con' (pres_names ++ names annm) config final_state
              else run 
                    (NonRedPCRed config
                      :<~| TaggerRed state_name tr_ng
                      :<~| LHRed abs_fun con' config) 
                    (DiscardIfAcceptedTag state_name
                      :<~> MaxOutputsHalter 
                      :<~> ZeroHalter 
                      :<~> LHHalter entry mb_modname (expr_env init_state)) 
                    NextOrderer 
                    con' (pres_names ++ names annm) config final_state
    
    -- We filter the returned states to only those with the minimal number of abstracted functions
    let mi = case length ret of
                  0 -> 0
                  _ -> minimum $ map (\(s, _, _, _) -> length $ abstract_calls $ track s) ret
    let ret' = filter (\(s, _, _, _) -> mi == (length $ abstract_calls $ track s)) ret

    let states = map (\(s, es, e, ais) -> (s {track = map (subVarFuncCall (model s) (expr_env s) (type_classes s)) $ abstract_calls $ track s}, es, e, ais)) ret'

    -- mapM (\(s, _, _, _) -> putStrLn . pprExecStateStr $ s) states
    -- mapM (\(_, es, e, ais) -> do print es; print e; print ais) states

    closeIO con

    return (states, ifi)

initializeLH :: [LHOutput] -> Lang.Id -> LHStateM [Lang.Name]
initializeLH ghci_cg ifi = do
    let ghcInfos = map ghcI ghci_cg

    addLHTC
    addOrdToNum

    let lh_measures = measureSpecs ghcInfos
    createMeasures lh_measures

    let specs = funcSpecs ghcInfos
    mergeLHSpecState specs

    addSpecialAsserts
    addTrueAsserts ifi

    -- getAnnotations ghci_cg

    -- The simplification works less well on some of the Core generated by convertCurrExpr,
    -- so we apply the simplification first
    simplify

    ns <- convertCurrExpr ifi

    return ns

getGHCInfos :: LHC.Config -> FilePath -> [FilePath] -> [FilePath] -> IO [LHOutput]
getGHCInfos config proj fp lhlibs = do
    let config' = config {idirs = idirs config ++ [proj] ++ lhlibs
                         , files = files config ++ lhlibs
                         , ghcOptions = ["-v"]}

    -- GhcInfo
    (ghci, _) <- LHI.getGhcInfos Nothing config' fp

    mapM (getGHCInfos' config') ghci


getGHCInfos' :: LHC.Config -> GhcInfo -> IO LHOutput
getGHCInfos' config ghci = do
    -- CGInfo
    -- let cgi = generateConstraints ghci

    -- finfo <- cgInfoFInfo ghci cgi
    -- F.Result _ sol _ <- solve (fixConfig "LH_FILEPATH" config) finfo

    return (LHOutput {ghcI = ghci, cgI = undefined {- cgi -}, solution = undefined {- sol -} })
    
funcSpecs :: [GhcInfo] -> [(Var, LocSpecType)]
funcSpecs = concatMap (gsTySigs . spec)

measureSpecs :: [GhcInfo] -> [Measure SpecType GHC.DataCon]
measureSpecs = concatMap (gsMeasures . spec)

reqNames :: State t -> [Name]
reqNames (State { expr_env = eenv
                , type_classes = tc
                , known_values = kv
                , apply_types = at }) = 
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
          (coerce tc :: M.Map Name Class)
      )
    ++ Lang.names at

pprint :: (Var, LocSpecType) -> IO ()
pprint (v, r) = do
    let i = mkIdUnsafe v

    let doc = PPR.rtypeDoc FPP.Full $ val r
    putStrLn $ show i
    putStrLn $ show doc

printLHOut :: Lang.Id -> [(State [FuncCall], [Expr], Expr, Maybe FuncCall)] -> IO ()
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
        putStrLn "when"
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

parseLHOut :: Lang.Id -> [(State [FuncCall], [Expr], Expr, Maybe FuncCall)] -> [LHReturn]
parseLHOut _ [] = []
parseLHOut entry ((s, inArg, ex, ais):xs) =
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

sameFuncNameArgs :: FuncInfo -> Maybe FuncInfo -> Bool
sameFuncNameArgs _ Nothing = False
sameFuncNameArgs (FuncInfo {func = f1, funcArgs = fa1}) (Just (FuncInfo {func = f2, funcArgs = fa2})) = f1 == f2 && fa1 == fa2

parseLHFuncTuple :: State t -> FuncCall -> FuncInfo
parseLHFuncTuple s (FuncCall {funcName = n, arguments = ars, returns = out}) =
    let
        t = case fmap typeOf $ E.lookup n (expr_env s) of
                  Just t' -> t'
                  Nothing -> error "Unknown type for abstracted function"
    in
    FuncInfo { func = nameOcc n
             , funcArgs = T.pack $ mkCleanExprHaskell s (foldl' App (Var (Id n t)) ars)
             , funcReturn = T.pack $ mkCleanExprHaskell s out }

testLiquidFile :: FilePath -> FilePath -> [FilePath] -> [FilePath] -> Config
               -> IO [LHReturn]
testLiquidFile proj fp libs lhlibs config = do
    lh_config <- getOpts []
    ghci_cg <- getGHCInfos lh_config proj [fp] lhlibs

    tgt_transv <- translateLoadedV proj fp libs False config

    let (mb_modname, pre_bnds, pre_tycons, pre_cls, tgt_lhs, tgt_ns, ex) = tgt_transv
    let tgt_trans = (mb_modname, pre_bnds, pre_tycons, pre_cls, tgt_ns, ex)

    putStrLn $ "******** Liquid File Test: *********"
    putStrLn fp

    let whitelist = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++
                    ['_', '\'']

    let blacklist = [
                      -- "group"
                      -- "toList",
                      -- "expand"
                      -- "minKeyList",
                      -- "minKeyMap"
                    ]

    let cleaned_tgt_lhs = filter (\n -> not $ elem n blacklist) $ 
                          filter (\n -> T.all (`elem` whitelist) n) tgt_lhs

    fmap concat $ mapM (\e -> do
        putStrLn $ show e
        runLHCore e tgt_trans ghci_cg config >>= (return . uncurry (flip parseLHOut) ))
                       cleaned_tgt_lhs

testLiquidDir :: FilePath -> FilePath -> [FilePath] -> [FilePath] -> Config
              -> IO [(FilePath, [LHReturn])]
testLiquidDir proj dir libs lhlibs config = do
  raw_files <- listDirectory dir
  let hs_files = filter (\a -> (".hs" `isSuffixOf` a) || (".lhs" `isSuffixOf` a)) raw_files
  
  results <- mapM (\fle -> do
      res <- testLiquidFile proj fle libs lhlibs config
      return (fle, res)
    ) hs_files

  return results
