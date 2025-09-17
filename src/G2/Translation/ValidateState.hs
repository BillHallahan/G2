{-# LANGUAGE OverloadedStrings, CPP #-}
module G2.Translation.ValidateState (
    loadSession,
    validateState,
    printStateOutput
) where

#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
import GHC.Driver.Session
#else
import DynFlags
import qualified EnumSet as ES
#endif

import GHC hiding (Id, entry)

import Control.Monad
import Data.Foldable (toList)
import Data.Maybe
import qualified Data.Sequence as S
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.HashMap.Lazy as H

import G2.Lib.Printers

import G2.Config
import G2.Language
import G2.Translation
import G2.Interface.ExecRes as I


loadSession :: GhcMonad m => [FilePath] -> [FilePath] -> String -> [GeneralFlag] -> m ()
loadSession proj src modN gflags = do 
    adjustDynFlags
    loadToCheck (map dirPath src ++ proj) src modN gflags

-- | Load the passed module(s) into GHC, and check that the `ExecRes` results are correct.
validateState :: GhcMonad m => String -> String -> [String] -> [String] -> Bindings
               -> ExecRes t
               -> m ( Maybe Bool -- ^ One bool per input `ExecRes`, indicating whether the results are correct or not
                                  -- Nothing in the case of a timeout
                     )
validateState modN entry chAll chAny b in_out = do
        let s = final_state in_out
        let pg = updatePGValNames (concatMap (map Data . dataCon) $ type_env s)
                       $ updatePGTypeNames (type_env s) $ mkPrettyGuide ()
        _ <- createDecls pg s (H.filter (\x -> adt_source x == ADTG2Generated) (type_env s))
        rs_anys <- validateStatesGHC pg (Just $ T.pack modN) entry chAll chAny b in_out
        
        return (fst rs_anys)

printStateOutput :: Config -> Id -> Bindings
               -> Maybe (Maybe Bool)
               -> ExecRes t
               -> IO ()
printStateOutput config entry b m_valid exec_res@(ExecRes { final_state = s }) = do
    let print_valid = isJust m_valid
    let val = fromMaybe (Just True) m_valid

    when print_valid (putStr (case val of
                                        Just True -> "✓ "
                                        Just False -> "✗ "
                                        Nothing -> "✗TO "))

    let pg = mkPrettyGuide (exprNames $ conc_args exec_res)
    let (mvp, inp, outp, handles) = printInputOutput pg entry b exec_res
        sym_gen_out = fmap (printHaskellPG pg s) $ conc_sym_gens exec_res
        
    let print_method = case print_output config of
                            True -> \m i o -> m <> i <> " = " <> o 
                            False -> \m i _ ->  m <> i

    case sym_gen_out of
        S.Empty -> T.putStrLn $ print_method mvp inp outp
        _ -> T.putStrLn $ print_method mvp inp outp <> "\t| generated: " <> T.intercalate ", " (toList sym_gen_out)
    if handles /= "" then T.putStrLn handles else return ()

            