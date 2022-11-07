{-# LANGUAGE CPP #-}

#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)

module G2.Translation.GHC ( module GHC
                          , module GHC.Core
                          , module GHC.Core.Class
                          , module GHC.Core.Coercion
                          , module GHC.Core.DataCon
                          , module GHC.Core.InstEnv
                          , module GHC.Core.TyCo.Rep
                          , module GHC.Core.TyCon
                          , module GHC.Data.FastString
                          , module GHC.Data.Pair
                          , module GHC.Driver.Config.Tidy
                          , module GHC.Driver.Main
                          , module GHC.Driver.Session
                          , module GHC.Iface.Tidy
                          , module GHC.Paths
                          , module GHC.Platform.Ways
                          , module GHC.Types.Avail
                          , module GHC.Types.Id.Info
                          , module GHC.Types.Literal
                          , module GHC.Types.Name
                          , module GHC.Types.SrcLoc
                          , module GHC.Types.Tickish
                          , module GHC.Types.TypeEnv
                          , module GHC.Types.Unique
                          , module GHC.Types.Var
                          , module GHC.Unit.Module.Deps
                          , module GHC.Unit.Module.ModDetails
                          , module GHC.Unit.Module.ModGuts
                          , module GHC.Unit.Types
                          
                          , HscTarget) where

import GHC
import GHC.Core ( Alt (..)
                , AltCon (..)
                , Bind (..)
                , CoreAlt
                , CoreBind
                , CoreExpr
                , CoreProgram
                , CoreRule (..)
                , Expr (..)
                
                , bindersOf)
import GHC.Core.Class (classAllSelIds, className, classSCTheta, classTyVars)
import GHC.Core.Coercion
import GHC.Core.DataCon
import GHC.Core.InstEnv
import GHC.Core.TyCo.Rep
import GHC.Core.TyCon
import GHC.Data.FastString
import GHC.Data.Pair
import GHC.Driver.Config.Tidy
import GHC.Driver.Main
import GHC.Driver.Session
import GHC.Iface.Tidy
import GHC.Paths
import GHC.Platform.Ways
import GHC.Types.Avail
import GHC.Types.Id.Info
import GHC.Types.Literal
import GHC.Types.Name hiding (varName)
import GHC.Types.SrcLoc
import GHC.Types.Tickish
import GHC.Types.TypeEnv
import GHC.Types.Unique
import GHC.Types.Var
import GHC.Unit.Module.Deps
import GHC.Unit.Module.ModDetails
import GHC.Unit.Module.ModGuts
import GHC.Unit.Types

type HscTarget = Backend

#else

module G2.Translation.GHC ( module Avail
                          , module Class
                          , module Coercion
                          , module CoreSyn
                          , module DataCon
                          , module DynFlags
                          , module FastString
                          , module GHC
                          , module GHC.Paths
                          , module HscMain
                          , module HscTypes
                          , module IdInfo
                          , module InstEnv
                          , module Literal
                          , module Name
                          , module Pair
                          , module SrcLoc
                          , module TidyPgm
                          , module TyCon
                          , module TyCoRep
                          , module Unique
                          , module Var) where

import Avail
import Class (classAllSelIds, className, classSCTheta, classTyVars)
import Coercion
import CoreSyn
import DataCon
import DynFlags
import FastString
import GHC hiding (AnnKeywordId (..), AnnExpr' (..))
import GHC.Paths
import HscMain
import HscTypes
import IdInfo
import InstEnv
import Literal
import Name hiding (varName)
import Pair
import SrcLoc
import TidyPgm
import TyCon
import TyCoRep
import Unique
import Var

#endif
