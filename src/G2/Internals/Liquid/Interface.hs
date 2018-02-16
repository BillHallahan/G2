{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Liquid.Interface where

import G2.Internals.Config.Config

import G2.Internals.Translation
import G2.Internals.Interface
import G2.Internals.Language as Lang
import G2.Internals.Execution
import G2.Internals.Liquid.Conversion
import G2.Internals.Liquid.ElimPartialApp
import G2.Internals.Liquid.Measures
import G2.Internals.Liquid.Rules
import G2.Internals.Liquid.SimplifyAsserts
import G2.Internals.Liquid.TCGen
import G2.Internals.Solver

import G2.Lib.Printers

import qualified Language.Haskell.Liquid.GHC.Interface as LHI
import Language.Haskell.Liquid.Types hiding (Config)
import qualified Language.Haskell.Liquid.Types.PrettyPrint as PPR
import Language.Haskell.Liquid.UX.CmdLine
import Language.Fixpoint.Types.PrettyPrint as FPP

import Data.Coerce
import Data.List
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.IO as TI
import qualified Data.Maybe as B

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
findCounterExamples :: FilePath -> FilePath -> FilePath -> T.Text -> [FilePath] -> [FilePath] -> Config -> IO [(State [(Name, [Expr], Expr)], [Rule], [Expr], Expr, Maybe (Name, [Expr], Expr))]
findCounterExamples proj primF fp entry libs lhlibs config = do
    ghcInfos <- getGHCInfos proj [fp] lhlibs
    tgt_trans <- translateLoaded proj fp primF libs False
    runLHCore entry tgt_trans ghcInfos config

runLHCore :: T.Text -> (Maybe T.Text, Program, [ProgramType], [(Name, Lang.Id, [Lang.Id])])
                    -> [GhcInfo]
                    -> Config
          -> IO [(State [(Name, [Expr], Expr)], [Rule], [Expr], Expr, Maybe (Name, [Expr], Expr))]
runLHCore entry (mb_modname, prog, tys, cls) ghcInfos config = do
    let specs = funcSpecs ghcInfos
    let lh_measures = measureSpecs ghcInfos
    -- let lh_measure_names = map (symbolName . val .name) lh_measures

    let init_state = initState prog tys cls Nothing Nothing Nothing True entry mb_modname
    let cleaned_state = (markAndSweepPreserving (reqNames init_state) init_state) { type_env = type_env init_state }
    let no_part_state = elimPartialApp cleaned_state
    let (lh_state, tcv) = createLHTC no_part_state
    let lhtc_state = addLHTC lh_state tcv
    let measure_state = createMeasures lh_measures tcv lhtc_state
    let (merged_state, mkv) = mergeLHSpecState specs measure_state tcv
    let beta_red_state = simplifyAsserts mkv merged_state

    let final_state = beta_red_state {track = []}

    (con, hhp) <- getSMT config

    ret <- run lhReduce con hhp config final_state

    -- We filter the returned states to only those with the minimal number of abstracted functions
    let mi = case length ret of
                  0 -> 0
                  _ -> minimum $ map (\(s, _, _, _, _) -> length $ track s) ret
    let ret' = filter (\(s, _, _, _, _) -> mi == (length $ track s)) ret

    return $ map (\(s, rs, es, e, ais) -> (s {track = subVar (model s) (expr_env s) $ track s}, rs, es, e, ais)) ret'

getGHCInfos :: FilePath -> [FilePath] -> [FilePath] -> IO [GhcInfo]
getGHCInfos proj fp lhlibs = do
    config <- getOpts []

    let config' = config {idirs = idirs config ++ [proj] ++ lhlibs
                         , files = files config ++ lhlibs
                         , ghcOptions = ["-v"]}
    return . fst =<< LHI.getGhcInfos Nothing config' fp
    
funcSpecs :: [GhcInfo] -> [(Var, LocSpecType)]
funcSpecs = concatMap (gsTySigs . spec)

measureSpecs :: [GhcInfo] -> [Measure SpecType GHC.DataCon]
measureSpecs = concatMap (gsMeasures . spec)

reqNames :: State t -> [Name]
reqNames (State { expr_env = eenv
                , type_classes = tc
                , known_values = kv }) = 
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
    Lang.names (M.filterWithKey (\k _ -> k == eqTC kv || k == numTC kv || k == ordTC kv || k == integralTC kv) (coerce tc :: M.Map Name Class))

pprint :: (Var, LocSpecType) -> IO ()
pprint (v, r) = do
    let i = mkIdUnsafe v

    let doc = PPR.rtypeDoc Full $ val r
    putStrLn $ show i
    putStrLn $ show doc

printLHOut :: T.Text -> [(State [(Name, [Expr], Expr)], [Rule], [Expr], Expr, Maybe (Name, [Expr], Expr))] -> IO ()
printLHOut entry = printParsedLHOut . parseLHOut entry

printParsedLHOut :: [LHReturn] -> IO ()
printParsedLHOut [] = return ()
printParsedLHOut (LHReturn { calledFunc = FuncInfo {func = f, funcArgs = call, funcReturn = output}
                           , violating = Nothing
                           , abstracted = abs} : xs) = do
    putStrLn "The call"
    TI.putStrLn $ call `T.append` " = " `T.append` output
    TI.putStrLn $ "violates " `T.append` f `T.append` "'s refinement type"
    printAbs abs
    putStrLn ""
    printParsedLHOut xs
printParsedLHOut (LHReturn { calledFunc = FuncInfo {func = f, funcArgs = call, funcReturn = output}
                           , violating = Just (FuncInfo {func = f', funcArgs = call', funcReturn = output'})
                           , abstracted = abs } : xs) = do
    TI.putStrLn $ call `T.append` " = " `T.append` output
    putStrLn "makes a call to"
    TI.putStrLn $ call' `T.append` " = " `T.append` output'
    TI.putStrLn $ "violating " `T.append` f' `T.append` "'s refinement type"
    printAbs abs
    putStrLn ""
    printParsedLHOut xs

printAbs :: [FuncInfo] -> IO ()
printAbs fi = do
    let fn = T.intercalate ", " $ map func fi

    if length fi > 0 then do
        putStrLn "when"
        mapM_ printFuncInfo fi
        if length fi > 1 then
            TI.putStrLn $ "Strengthen the refinement types of " `T.append` fn `T.append` " to eliminate these possibilities"
        else
            TI.putStrLn $ "Strengthen the refinement type of " `T.append` fn `T.append` " to eliminate this possibility"
    else
        return () 

printFuncInfo :: FuncInfo -> IO ()
printFuncInfo (FuncInfo {funcArgs = call, funcReturn = output}) =
    TI.putStrLn $ call `T.append` " = " `T.append` output

parseLHOut :: T.Text -> [(State [(Name, [Expr], Expr)], [Rule], [Expr], Expr, Maybe (Name, [Expr], Expr))]
           -> [LHReturn]
parseLHOut entry [] = []
parseLHOut entry ((s, _, inArg, ex, ais):xs) =
  let tail = parseLHOut entry xs
      funcCall = T.pack $ mkCleanExprHaskell (known_values s) (type_classes s) 
               . foldl (\a a' -> App a a') (Var $ Id (Name entry Nothing 0) TyBottom) $ inArg
      funcOut = T.pack $ mkCleanExprHaskell (known_values s) (type_classes s) $ ex


      called = FuncInfo {func = entry, funcArgs = funcCall, funcReturn = funcOut}
      viFunc = fmap (parseLHFuncTuple s) ais

      abs = map (parseLHFuncTuple s) $ track s
  in 
  LHReturn { calledFunc = called
           , violating = if Just called == viFunc then Nothing else viFunc
           , abstracted = abs} : tail

parseLHFuncTuple :: State t -> (Name, [Expr], Expr) -> FuncInfo
parseLHFuncTuple s (n@(Name n' _ _), ais, out) =
    FuncInfo { func = n'
             , funcArgs = T.pack $ mkCleanExprHaskell (known_values s) (type_classes s) (foldl' App (Var (Id n TyBottom)) ais)
             , funcReturn = T.pack $ mkCleanExprHaskell (known_values s) (type_classes s) out }

testLiquidFile :: FilePath -> FilePath -> FilePath -> [FilePath] -> [FilePath] -> Config
               -> IO [LHReturn]
testLiquidFile proj primF fp libs lhlibs config = do
    ghcInfos <- getGHCInfos proj [fp] lhlibs
    tgt_transv <- translateLoadedV proj fp primF libs False

    let (mb_modname, pre_bnds, pre_tycons, pre_cls, tgt_lhs) = tgt_transv
    let tgt_trans = (mb_modname, pre_bnds, pre_tycons, pre_cls)

    putStrLn $ "******** Liquid File Test: *********"
    putStrLn fp

    let whitelist = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] 

    let cleaned_tgt_lhs = filter (\n -> T.all (`elem` whitelist) n) tgt_lhs

    fmap concat $ mapM (\e -> runLHCore e tgt_trans ghcInfos config >>= (return . parseLHOut e))
                       cleaned_tgt_lhs

testLiquidDir :: FilePath -> FilePath -> FilePath -> [FilePath] -> [FilePath] -> Config
              -> IO [(FilePath, [LHReturn])]
testLiquidDir proj primF dir libs lhlibs config = do
  raw_files <- listDirectory dir
  let hs_files = filter (\a -> (".hs" `isSuffixOf` a) || (".lhs" `isSuffixOf` a)) raw_files
  
  results <- mapM (\file -> do
      res <- testLiquidFile proj primF file libs lhlibs config
      return (file, res)
    ) hs_files

  return results

