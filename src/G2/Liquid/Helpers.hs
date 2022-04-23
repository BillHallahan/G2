{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}

module G2.Liquid.Helpers ( MeasureSymbols (..)
                         , getGHCInfos
                         , funcSpecs
                         
                         , getTySigs
                         , putTySigs
                         , getAssumedSigs
                         , putAssumedSigs
                         , getQualifiers
                         , putQualifiers
                         , findFuncSpec
                         , measureSpecs
                         , measureSymbols
                         , measureNames
                         , varToName
                         , varEqName
                         , namesEq
                         , fillLHDictArgs ) where

import G2.Language as G2
import G2.Translation.Haskell

import qualified Language.Haskell.Liquid.GHC.Interface as LHI
import Language.Fixpoint.Types.Names
import Language.Haskell.Liquid.Types hiding (Config, cls, names)
import qualified Language.Haskell.Liquid.UX.Config as LHC
import Language.Fixpoint.Types (Qualifier (..))

import Data.List
import qualified Data.Map as M
import qualified Data.Text as T

import GHC as GHC
import Name
import Var as V

import Debug.Trace

-- | Interface with LH
getGHCInfos :: LHC.Config -> [FilePath] -> [FilePath] -> [FilePath] -> IO [GhcInfo]
getGHCInfos config proj fp lhlibs = do
    let config' = config {idirs = idirs config ++ proj ++ lhlibs
                         , files = files config ++ lhlibs
                         , ghcOptions = ["-v"]}

    -- GhcInfo
    (ghci, _) <- LHI.getGhcInfos Nothing config' fp

    return ghci
    
funcSpecs :: [GhcInfo] -> [(Var, LocSpecType)]
funcSpecs fs =
    let
        asserted = concatMap getTySigs fs
        assumed = concatMap getAssumedSigs fs
    in
    asserted ++ assumed

-- | Functions asserted in LH
getTySigs :: GhcInfo -> [(Var, LocSpecType)]
#if MIN_VERSION_liquidhaskell(0,8,6)
getTySigs = gsTySigs . gsSig . giSpec
#else
getTySigs = gsTySigs . spec
#endif

putTySigs :: GhcInfo -> [(Var, LocSpecType)] -> GhcInfo
#if MIN_VERSION_liquidhaskell(0,8,6)
putTySigs gi@(GI {
                    giSpec = sp@(SP { gsSig = sp_sig })
                 }
             ) new_ty_sigs = 
    gi { giSpec = sp { gsSig = sp_sig { gsTySigs = new_ty_sigs } } }
#else
putTySigs gi@(GI { spec = sp }) new_ty_sigs = 
    gi { spec = sp { gsTySigs = new_ty_sigs }}
#endif

-- | Functions assumed in LH
getAssumedSigs :: GhcInfo -> [(Var, LocSpecType)]
#if MIN_VERSION_liquidhaskell(0,8,6)
getAssumedSigs = gsAsmSigs . gsSig . giSpec
#else
getAssumedSigs = gsAsmSigs . spec
#endif

putAssumedSigs :: GhcInfo -> [(Var, LocSpecType)] -> GhcInfo
#if MIN_VERSION_liquidhaskell(0,8,6)
putAssumedSigs gi@(GI {
                    giSpec = sp@(SP { gsSig = sp_sig })
                 }
             ) new_ty_sigs = 
    gi { giSpec = sp { gsSig = sp_sig { gsTySigs = new_ty_sigs } } }
#else
putAssumedSigs gi@(GI { spec = sp }) new_ty_sigs = 
    gi { spec = sp { gsTySigs = new_ty_sigs }}
#endif

getQualifiers :: GhcInfo -> [Qualifier]
#if MIN_VERSION_liquidhaskell(0,8,6)
getQualifiers = gsQualifiers . gsQual . giSpec
#else
getQualifiers = gsQualifiers . spec
#endif

putQualifiers :: GhcInfo -> [Qualifier] -> GhcInfo
#if MIN_VERSION_liquidhaskell(0,8,6)
putQualifiers gi@(GI {
                    giSpec = sp@(SP { gsQual = quals })
                 }
             ) new_quals = 
    gi { giSpec = sp { gsQual = quals { gsQualifiers = new_quals } } }
#else
putQualifiers gi@(GI { spec = sp }) new_quals = 
    gi { spec = sp { gsQualifiers = new_quals }}
#endif


findFuncSpec :: [GhcInfo] -> G2.Name -> Maybe SpecType
findFuncSpec ghci g2_n =
    let
        fs = funcSpecs ghci
        fs' = map (\(v, lst) -> (V.varName v, lst)) fs
    in
    case find (\(n, _) -> namesEq n g2_n) fs' of
        Just st -> Just . val . snd $ st
        Nothing -> Nothing

varToName :: V.Var -> G2.Name
varToName = mkName . V.varName

varEqName :: V.Var -> G2.Name -> Bool
varEqName v = namesEq (V.varName v)

namesEq :: GHC.Name -> G2.Name -> Bool
namesEq ghc_n (Name n m _ _) =
    T.pack (occNameString $ nameOccName ghc_n) == n
        && (case nameModule_maybe ghc_n of
                Just mod ->
                    Just (T.pack . moduleNameString . moduleName $ mod) == m
                Nothing -> m == Nothing)

measureSpecs :: [GhcInfo] -> [Measure SpecType GHC.DataCon]
#if MIN_VERSION_liquidhaskell(0,8,6)
measureSpecs = concatMap (gsMeasures . gsData . giSpec)
#else
measureSpecs = concatMap (gsMeasures . spec)
#endif

newtype MeasureSymbols = MeasureSymbols { symbols :: [Symbol] }

measureSymbols :: [GhcInfo] -> MeasureSymbols
measureSymbols = MeasureSymbols . measureNames

measureNames :: [GhcInfo] -> [Symbol]
#if MIN_VERSION_liquidhaskell(0,8,6) || defined NEW_LH
measureNames = map (val . msName) . measureSpecs
#else
measureNames = map (val . name) . measureSpecs
#endif

-- The walk function takes lhDict arguments that are not correctly accounted for by mkStrict.
-- The arguments are not actually used, so, here, we fill them in with undefined. 
fillLHDictArgs :: Walkers -> Expr -> Expr
fillLHDictArgs w = modifyAppTop (fillLHDictArgs' w)

fillLHDictArgs' :: Walkers -> Expr -> Expr
fillLHDictArgs' w e
    | f@(Var i):xs <- unApp e
    , any (\(_, i') -> i == i') (M.toList w) = mkApp $ f:fillLHDictArgs'' 0 xs
    | otherwise = e

fillLHDictArgs'' :: Int -> [Expr] -> [Expr]
fillLHDictArgs'' !n [] = replicate n (Prim Undefined TyBottom)
fillLHDictArgs'' !n (t@(Type _):xs) = t:fillLHDictArgs'' (n + 1) xs
fillLHDictArgs'' !n xs = replicate n (Prim Undefined TyBottom) ++ xs
