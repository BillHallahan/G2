module Main where

import System.Environment

import HscTypes
import TyCon
import GHC hiding (Name, Type, exprType)

import Data.List
import qualified Data.Map as M
import Data.Tuple

import G2.Lib.Utils
import G2.Lib.Printers

import G2.Internals.Interface
import G2.Internals.Core
import G2.Internals.Translation
import G2.Internals.Preprocessing
import G2.Internals.Symbolic
import G2.Internals.SMT

main = do
    (proj:src:entry:tail_args) <- getArgs

    let n_val = nVal tail_args
    let m_assume = mAssume tail_args
    let m_assert = mAssert tail_args

    (tenv, eenv, varN, conN) <- hskToG2 proj src

    let revVarN = M.fromList . map swap $ M.toList varN

    let entry' = lookupFromNamesMap varN entry
    let assume = return . lookupFromNamesMap varN =<< m_assume
    let assert = return . lookupFromNamesMap varN =<< m_assert

    let init_state = initState tenv eenv assume assert entry'

    hhp <- getZ3ProcessHandles

    in_out <- run smt2 hhp n_val init_state

    mapM_ (\(inArg, ex) -> do
            let inArg' = map (maybeReplaceVarName revVarN) . map (replaceDataConName conN) $ inArg
            let ex' = replaceDataConName conN ex

            let funcCall = mkExprHaskell 
                             . foldl (\a a' -> App a a') (Var entry TyBottom) $ inArg'

            let funcOut = mkExprHaskell $ ex'

            putStrLn (funcCall ++ " == " ++ funcOut)
        ) in_out


mArg :: String -> [String] -> (String -> a) -> a -> a
mArg s args f d = case elemIndex s args of
               Nothing -> d
               Just id -> if id >= length args
                              then error ("Invalid use of " ++ s)
                              else f (args !! (id + 1))

lookupFromNamesMap :: M.Map Name Name -> Name -> Name
lookupFromNamesMap nMap n =
    case M.lookup n nMap of
                Just f -> f
                Nothing -> error (n ++ " not recognized.")

maybeReplaceVarName :: M.Map Name Name -> Expr -> Expr
maybeReplaceVarName nMap v@(Var n t) =
    case M.lookup n nMap of
        Just n' -> Var n' t
        Nothing -> v
maybeReplaceVarName _ e = e

replaceDataConName :: M.Map Name Name -> Expr -> Expr
replaceDataConName conMap = modify (replaceDataConName' conMap)
    where
        replaceDataConName' :: M.Map Name Name -> Expr -> Expr
        replaceDataConName' conMap (Data (DataCon n i t ts)) =
            case M.lookup n conMap of
                        Just n' -> (Data (DataCon n' i t ts))
                        Nothing -> error (n ++ " not recognized.")
        replaceDataConName' _ e = e

nVal :: [String] -> Int
nVal args = mArg "--n" args read 200

mAssume :: [String] -> Maybe String
mAssume args = mArg "--assume" args Just Nothing

mAssert :: [String] -> Maybe String
mAssert args = mArg "--assert" args Just Nothing
