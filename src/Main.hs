module Main where

import System.Environment

import Data.List
import Data.Maybe

import System.Directory

import G2.Lib.Printers

import G2.Internals.Execution
import G2.Internals.Interface
import G2.Internals.Language
import G2.Internals.Language.ExprEnv as E
import G2.Internals.Translation
import G2.Internals.Solver

import G2.Internals.Liquid.Interface


eApp = 
    App 
        (App 
            (App 
                (Var 
                    (Id 
                        (Name "sget" (Just "SimplePoly") 8214565720323795719) 
                        (TyFun 
                            (TyConApp (Name "LH" Nothing 0) [TyVar (Id (Name "a" Nothing 6989586621679022893) TYPE)]) 
                            (TyFun 
                                (TyVar (Id (Name "a" Nothing 6989586621679022893) TYPE)) 
                                (TyFun 
                                    (TyConApp (Name "S" (Just "SimplePoly") 8214565720323795712) [TyVar (Id (Name "a" Nothing 6989586621679022893) TYPE)]) 
                                    (TyVar (Id (Name "a" Nothing 6989586621679022893) TYPE))
                                )
                            )
                        )
                    )
                ) 
                (Var 
                    (Id 
                        (Name "lhIntFunc" Nothing 0) 
                        (TyConApp (Name "LH" Nothing 0) [TyConApp (Name "Int" (Just "GHC.Types") 3674937295934324766) []])
                    )
                )
            ) 
            (Type (TyConApp (Name "Int" (Just "GHC.Types") 3674937295934324766) []))
        ) 
        (Var 
            (Id 
                (Name "s" (Just "") 0) 
                (TyConApp (Name "S" (Just "SimplePoly") 8214565720323786251) [TyConApp (Name "Int" (Just "GHC.Types") 3674937295934324766) []])
            )
        )


main :: IO ()
main = do
    as <- getArgs
    let (proj:prims:_) = as

    -- as@(proj:prims:_) <- getArgs
    -- home_dir <- getHomeDirectory
    -- prepBase $ home_dir ++ "/Desktop/base.tar.gz"

    let m_liquid = mkLiquid as
    let m_liquid_func = mkLiquidFunc as

    case (m_liquid, m_liquid_func) of
        (Just l, Just f) -> do
            -- ghcInfos <- getGHCInfos [l]
            -- putStrLn . show $ length ghcInfos

            -- let specs = funcSpecs ghcInfos
            -- mapM_ (\s -> do
            --     putStrLn ""
            --     pprint s) specs

            ---------

            let n_val = nVal as

            in_out <- findCounterExamples proj prims l f n_val

            printFuncCalls f in_out
            
    
        _ -> runGHC as

runGHC :: [String] -> IO ()
runGHC as = do
    let (proj:src:lib:entry:tail_args) = as

    --Get args
    let n_val = nVal tail_args
    let m_assume = mAssume tail_args
    let m_assert = mAssert tail_args
    let m_reaches = mReaches tail_args

    let m_wrapper = mWrapper tail_args
    let m_wrap_with = mWrapWith tail_args
    let m_wrap_i = mWrapperInt tail_args

    let m_poly_pred = mkPolyPred tail_args
    let m_poly_pred_with = mkPolyPredWith tail_args
    let m_poly_pred_i = mkPolyPredInt tail_args

    (binds, tycons, cls) <- translateLoaded proj src lib True
    -- (binds, tycons) <- translation proj src
    
    let init_state = initState binds tycons cls m_assume m_assert m_reaches (isJust m_assert || isJust m_reaches) entry

    let init_state' = case (m_wrapper, m_wrap_with) of
                            (Just w, Just ww) -> case (findFunc w (expr_env init_state), findFunc ww (expr_env init_state)) of
                                (Left (Id n _, _), Left (wwi, _)) -> addHigherOrderWrappers init_state n wwi m_wrap_i
                                _ -> init_state
                            _ -> init_state


    let init_state'' = case (m_poly_pred, m_poly_pred_with) of
                            (Just p, Just pw) -> case (findFunc p (expr_env init_state), findFunc pw (expr_env init_state)) of
                                (Left (Id n _, _), Left (ppi, _)) -> addPolyPred init_state n ppi m_poly_pred_i
                                _ -> init_state'
                            _ -> init_state'

    hhp <- getZ3ProcessHandles

    in_out <- run smt2 hhp n_val init_state''

    -- putStrLn "----------------\n----------------"

    printFuncCalls entry in_out


printFuncCalls :: String -> [(State, [Rule], [Expr], Expr)] -> IO ()
printFuncCalls entry =
    mapM_ (\(s, _, inArg, ex) -> do
        let funcCall = mkExprHaskell 
                     . foldl (\a a' -> App a a') (Var $ Id (Name entry Nothing 0) TyBottom) $ inArg

        let funcOut = mkExprHaskell $ ex

        -- print $ model s
        -- print inArg
        -- print ex

        putStrLn $ funcCall ++ " = " ++ funcOut)

mArg :: String -> [String] -> (String -> a) -> a -> a
mArg s a f d = case elemIndex s a of
               Nothing -> d
               Just i -> if i >= length a
                              then error ("Invalid use of " ++ s)
                              else f (a !! (i + 1))

nVal :: [String] -> Int
nVal a = mArg "--n" a read 500

mAssume :: [String] -> Maybe String
mAssume a = mArg "--assume" a Just Nothing

mAssert :: [String] -> Maybe String
mAssert a = mArg "--assert" a Just Nothing

mReaches :: [String] -> Maybe String
mReaches a = mArg "--reaches" a Just Nothing

mWrapper :: [String] -> Maybe String
mWrapper a = mArg "--wrapper" a Just Nothing

mWrapWith :: [String] -> Maybe String
mWrapWith a = mArg "--wrap-with" a Just Nothing

mWrapperInt :: [String] -> Int
mWrapperInt a = mArg "--wrap-i" a read (-1)

mkPolyPred :: [String] -> Maybe String
mkPolyPred a = mArg "--poly-pred" a Just Nothing

mkPolyPredWith :: [String] -> Maybe String
mkPolyPredWith a = mArg "--poly-pred-with" a Just Nothing

mkPolyPredInt :: [String] -> Int
mkPolyPredInt a = mArg "--poly-pred-i" a read (-1)

mkLiquid :: [String] -> Maybe String
mkLiquid a = mArg "--liquid" a Just Nothing

mkLiquidFunc :: [String] -> Maybe String
mkLiquidFunc a = mArg "--liquid-func" a Just Nothing
