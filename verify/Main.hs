{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module Main (main) where

import Data.Foldable (toList)
import qualified Data.Sequence as S
import qualified Data.Text as T
import qualified Data.Text.IO as T

import G2.Lib.Printers

import G2.Config
import G2.Interface
import G2.Language
import G2.Translation
import G2.Verify.Config
import G2.Verify.Interface

main :: IO ()
main = do
  (src, entry, verify_config, config) <- getVerifyConfigs

  proj <- guessProj (includePaths config) src

  let tentry = T.pack entry

  (vr, b, entry_f) <- verifyFromFile proj [src] tentry simplTranslationConfig config verify_config
  
  case vr of
    Verified -> putStrLn "Verified"
    VerifyTimeOut -> putStrLn "Unknown (Timeout)"
    Counterexample ce -> do putStrLn "Counterexample"; printFuncCalls config entry_f b ce
  

printFuncCalls :: Config -> Id -> Bindings
               -> [ExecRes t]
               -> IO ()
printFuncCalls config entry b exec_res = do
    mapM_ (\execr@(ExecRes { final_state = s }) -> do
        let pg = mkPrettyGuide (exprNames $ conc_args execr)
        let (mvp, inp, outp, hdls) = printInputOutput pg entry b execr
            sym_gen_out = fmap (printHaskellPG pg s) $ conc_sym_gens execr

        let print_method = case print_output config of
                                True -> \m i o -> m <> i <> " = " <> o 
                                False -> \m i _ ->  m <> i

        case sym_gen_out of
            S.Empty -> T.putStrLn $ print_method mvp inp outp
            _ -> T.putStrLn $ print_method mvp inp outp <> "\t| generated: " <> T.intercalate ", " (toList sym_gen_out)
        if hdls /= "" then T.putStrLn hdls else return ())
      $ exec_res