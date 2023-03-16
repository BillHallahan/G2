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
import G2.Liquid.Types
import G2.Translation.Haskell

#if MIN_VERSION_liquidhaskell(0,9,0)
import qualified Liquid.GHC.Interface as LHI
#else
import qualified Language.Haskell.Liquid.GHC.Interface as LHI
#endif
import Language.Fixpoint.Types.Names
#if MIN_VERSION_liquidhaskell(0,8,10)
import Language.Haskell.Liquid.Types hiding
        (Config, TargetInfo (..), TargetSpec (..), GhcSpec (..), cls, names)
#else
import Language.Haskell.Liquid.Types
#endif
import qualified Language.Haskell.Liquid.UX.Config as LHC
import Language.Fixpoint.Types (Qualifier (..))

import Data.List
import qualified Data.Map as M
import qualified Data.Text as T

import GHC as GHC
#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
import GHC.Types.Name
import GHC.Types.Var as V
#else
import Name
import Var as V
#endif

-- | Interface with LH
getGHCInfos :: LHC.Config -> [FilePath] -> [FilePath] -> IO [GhcInfo]
getGHCInfos config proj fp = do
    let config' = config {idirs = idirs config ++ proj
                         , files = files config
                         , ghcOptions = ["-v"]}

    -- GhcInfo
#if MIN_VERSION_liquidhaskell(0,8,10)
    (ghci, _) <- LHI.getTargetInfos Nothing config' fp
#else
    (ghci, _) <- LHI.getGhcInfos Nothing config' fp
#endif

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
                Just m' ->
                    Just (T.pack . moduleNameString . moduleName $ m') == m
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
#if MIN_VERSION_liquidhaskell(0,8,6)
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
