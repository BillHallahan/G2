{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module Main (main) where

import G2.Translation.GHC (GeneralFlag(Opt_Hpc))

import System.Environment
import System.FilePath

import Control.Monad
import Data.Foldable (toList)
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid ((<>))
import qualified Data.Sequence as S
import qualified Data.Text as T
import qualified Data.Text.IO as T

import G2.Lib.Printers

import G2.Config
import G2.Interface
import G2.Language
import G2.Translation

main :: IO ()
main = do
  as <- getArgs
  runWithArgs as

runWithArgs :: [String] -> IO ()
runWithArgs as = do
  let (_:_:tail_args) = as
  (src, entry, m_assume, m_assert, config) <- getConfig

  proj <- guessProj (includePaths config) src

  --Get args
  let m_reaches = mReaches tail_args
  let m_retsTrue = mReturnsTrue tail_args

  let tentry = T.pack entry

  (in_out, b, _, entry_f@(Id (Name _ mb_modname _ _) _)) <-
        runG2FromFile proj [src] (fmap T.pack m_assume)
                  (fmap T.pack m_assert) (fmap T.pack m_reaches) 
                  (isJust m_assert || isJust m_reaches || m_retsTrue) 
                  tentry simplTranslationConfig config

  let in_out' = if print_encode_float config then toEnclodeFloats in_out else in_out

  let (unspecified_output, spec_output) = L.partition (\ExecRes { final_state = s } -> getExpr s == Prim UnspecifiedOutput TyBottom) in_out'
  
  when (print_num_post_call_func_arg config) $ do
        putStrLn $ "Post call states: " ++ show (length spec_output)
        putStrLn $ "Func arg states: " ++ show (length unspecified_output)

  val_res <- case validate config || measure_coverage config of
                True -> do
                    r <- validateStates proj [src] (T.unpack $ fromJust mb_modname) entry [] [Opt_Hpc] b in_out'
                    if all isJust r && and (map fromJust r) then putStrLn "Validated" else putStrLn "There was an error during validation."

                    if any isNothing r then putStrLn $ "Timeout count: " ++ show (length $ filter isNothing r) else return ()

                    printFuncCalls config entry_f b (Just r) in_out'
                    return (Just r)
                False -> do
                    printFuncCalls config entry_f b Nothing in_out'
                    return Nothing

  when (measure_coverage config) $
    case val_res of
        Just vals -> runHPC src (T.unpack $ fromJust mb_modname) entry . map snd . filter (fromMaybe False . fst) $ zip vals in_out'
        Nothing -> error "Impossible: validate must have run"

printFuncCalls :: Config -> Id -> Bindings
               -> Maybe [Maybe Bool]
               -> [ExecRes t]
               -> IO ()
printFuncCalls config entry b m_valid exec_res = do
    let valid = fromMaybe (repeat (Just True)) m_valid
        print_valid = isJust m_valid

    mapM_ (\(execr@(ExecRes { final_state = s }), val) -> do
        when print_valid (putStr (case val of
                                        Just True -> "✓ "
                                        Just False -> "✗ "
                                        Nothing -> "✗TO "))

        let pg = mkPrettyGuide (exprNames $ conc_args execr)
        let (mvp, inp, outp, handles) = printInputOutput pg entry b execr
            sym_gen_out = fmap (printHaskellPG pg s) $ conc_sym_gens execr

        let print_method = case print_output config of
                                True -> \m i o -> m <> i <> " = " <> o 
                                False -> \m i _ ->  m <> i

        case sym_gen_out of
            S.Empty -> T.putStrLn $ print_method mvp inp outp
            _ -> T.putStrLn $ print_method mvp inp outp <> "\t| generated: " <> T.intercalate ", " (toList sym_gen_out)
        if handles /= "" then T.putStrLn handles else return ())
      $ zip exec_res valid

toEnclodeFloats :: ASTContainer m Expr => m -> m
toEnclodeFloats = modifyASTs go
    where
        go (App (Data (DataCon { dc_name = dcn })) (Lit (LitFloat f)))
            | not (isNaN f), not (isInfinite f), not (isNegativeZero f), nameOcc dcn == "F#" =
                let (m, n) = decodeFloat f in mkApp [encFloat, iCon $ Lit (LitInteger m), iCon $ Lit (LitInt $ toInteger n)]
        go (App (Data (DataCon { dc_name = dcn })) (Lit (LitDouble f)))
            | not (isNaN f), not (isInfinite f), not (isNegativeZero f), nameOcc dcn == "D#" =
                let (m, n) = decodeFloat f in mkApp [encFloat, iCon $ Lit (LitInteger m), iCon $ Lit (LitInt $ toInteger n)]
        go (Lit (LitFloat f))
            | not (isNaN f), not (isInfinite f), not (isNegativeZero f) =
                let (m, n) = decodeFloat f in mkApp [encFloat, iCon $ Lit (LitInteger m), iCon $ Lit (LitInt $ toInteger n)]
        go (Lit (LitDouble f))
            | not (isNaN f), not (isInfinite f), not (isNegativeZero f) =
                let (m, n) = decodeFloat f in mkApp [encFloat, iCon $ Lit (LitInteger m), iCon $ Lit (LitInt $ toInteger n)]
        go e = e

        iCon = App (Data (DataCon { dc_name = Name "Z#" Nothing 0 Nothing, dc_type = TyUnknown, dc_exist_tyvars = [], dc_univ_tyvars = [] }))
        encFloat = Var (Id (Name "encodeFloat" Nothing 0 Nothing) TyUnknown)

mReturnsTrue :: [String] -> Bool
mReturnsTrue a = boolArg "returns-true" a M.empty Off

mReaches :: [String] -> Maybe String
mReaches a = strArg "reaches" a M.empty Just Nothing