{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Liquid.Interface where

import G2.Internals.Config.Config

import G2.Internals.Translation
import G2.Internals.Interface
import G2.Internals.Language as Lang
import G2.Internals.Execution
import G2.Internals.Liquid.Conversion
import G2.Internals.Liquid.Measures
import G2.Internals.Liquid.ElimPartialApp
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
import qualified Data.Maybe as B

import System.Directory

import qualified GHC as GHC
import Var

import G2.Internals.Language.KnownValues

-- | findCounterExamples
-- Given (several) LH sources, and a string specifying a function name,
-- attempt to find counterexamples to the functions liquid type
findCounterExamples :: FilePath -> FilePath -> FilePath -> T.Text -> [FilePath] -> [FilePath] -> Config -> IO [(State (), [Rule], [Expr], Expr, Maybe (Name, [Expr], Expr))]
findCounterExamples proj primF fp entry libs lhlibs config = do
    ghcInfos <- getGHCInfos proj [fp] lhlibs
    tgt_trans <- translateLoaded proj fp primF libs False
    runLHCore entry tgt_trans ghcInfos config

runLHCore :: T.Text -> (Maybe T.Text, Program, [ProgramType], [(Name, Lang.Id, [Lang.Id])])
                    -> [GhcInfo]
                    -> Config
          -> IO [(State (), [Rule], [Expr], Expr, Maybe (Name, [Expr], Expr))]
runLHCore entry (mb_modname, prog, tys, cls) ghcInfos config = do
    let specs = funcSpecs ghcInfos
    let lh_measures = measureSpecs ghcInfos

    let init_state = initState prog tys cls Nothing Nothing Nothing True entry mb_modname
    let cleaned_state = (markAndSweepPreserving (reqNames init_state) init_state) { type_env = type_env init_state }
    let no_part_state = elimPartialApp cleaned_state
    let (lh_state, tcv) = createLHTC no_part_state
    let lhtc_state = addLHTC lh_state tcv
    let measure_state = createMeasures lh_measures tcv lhtc_state
    let (merged_state, mkv) = mergeLHSpecState specs measure_state tcv
    let beta_red_state = simplifyAsserts mkv merged_state

    (con, hhp) <- getSMT config

    run con hhp config beta_red_state

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

printLHOut :: T.Text -> [(State t, [Rule], [Expr], Expr, Maybe (Name, [Expr], Expr))] -> IO ()
printLHOut entry = printParsedLHOut . parseLHOut entry

printParsedLHOut :: [Either (T.Text, T.Text, T.Text)
                            ((T.Text, T.Text, T.Text), (T.Text, T.Text, T.Text))]
                 -> IO ()
printParsedLHOut [] = return ()
printParsedLHOut ((Left (f, call, output)):xs) = do
    putStrLn "The call"
    putStrLn . T.unpack $ call `T.append` " = " `T.append` output
    putStrLn . T.unpack $ "violates " `T.append` f `T.append` "'s refinement type"
    putStrLn ""
    printParsedLHOut xs
printParsedLHOut ((Right ((f, call, output), (f', call', output'))):xs) = do
    putStrLn . T.unpack $ call `T.append` " = " `T.append` output
    putStrLn "makes a call to"
    putStrLn . T.unpack $ call' `T.append` " = " `T.append` output'
    putStrLn . T.unpack $ "violating " `T.append` f' `T.append` "'s refinement type"
    putStrLn ""
    printParsedLHOut xs

parseLHOut :: T.Text -> [(State t, [Rule], [Expr], Expr, Maybe (Name, [Expr], Expr))]
           -> [Either (T.Text, T.Text, T.Text)
                      ((T.Text, T.Text, T.Text), (T.Text, T.Text, T.Text))]
parseLHOut entry [] = []
parseLHOut entry ((s, _, inArg, ex, ais):xs) =
  let tail = parseLHOut entry xs
      funcCall = T.pack $ mkCleanExprHaskell (known_values s) (type_classes s) 
               . foldl (\a a' -> App a a') (Var $ Id (Name entry Nothing 0) TyBottom) $ inArg
      funcOut = T.pack $ mkCleanExprHaskell (known_values s) (type_classes s) $ ex
      (n, as, out) = (case ais of
        Just (n'@(Name n'' _ _), ais', out') -> 
          ( n''
          , T.pack $ mkCleanExprHaskell (known_values s) (type_classes s) (foldl' App (Var (Id n' TyBottom)) ais')
          , T.pack $ mkCleanExprHaskell (known_values s) (type_classes s) out')
        _ -> (T.pack "", T.pack "", T.pack ""))
   in 
   if funcCall == as && funcOut == out then do
      Left (entry, funcCall, funcOut) : tail
   else
      Right ((entry, funcCall, funcOut), (n, as, out)) : tail

testLiquidFile :: FilePath -> FilePath -> FilePath -> [FilePath] -> [FilePath] -> Config
               -> IO [Either (T.Text, T.Text, T.Text)
                             ((T.Text, T.Text, T.Text), (T.Text, T.Text, T.Text))]
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
              -> IO [(FilePath, [Either (T.Text, T.Text, T.Text)
                                        ((T.Text, T.Text, T.Text), (T.Text, T.Text, T.Text))])]
testLiquidDir proj primF dir libs lhlibs config = do
  raw_files <- listDirectory dir
  let hs_files = filter (\a -> (".hs" `isSuffixOf` a) || (".lhs" `isSuffixOf` a)) raw_files
  
  results <- mapM (\file -> do
      res <- testLiquidFile proj primF file libs lhlibs config
      return (file, res)
    ) hs_files

  return results

