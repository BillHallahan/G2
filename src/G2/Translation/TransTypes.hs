module G2.Translation.TransTypes where

import CoreSyn
import GHC
import HscTypes

import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T

import qualified G2.Language as G2

type NameMap = HM.HashMap (T.Text, Maybe T.Text) G2.Name

type TypeNameMap = HM.HashMap (T.Text, Maybe T.Text) G2.Name

type ExportedName = G2.Name


data ModGutsClosure = ModGutsClosure
  { mgcc_mod_name :: Maybe String
  , mgcc_binds :: [CoreBind]
  , mgcc_tycons :: [TyCon]
  , mgcc_breaks :: Maybe ModBreaks
  , mgcc_cls_insts :: [ClsInst]
  , mgcc_type_env :: TypeEnv
  , mgcc_exports :: [ExportedName]
  }


-- Data necessary from Ghc to compile Haskell module(s) into G2 Core
data CompileClosure = CompileClosure
  { mod_name :: Maybe String
  , tycon_data :: [[TyCon]]
  , bindings :: [([CoreBind], Maybe ModBreaks)]
  , cls_inst :: [ClsInst]
  , mod_det_types :: [TypeEnv]
  , exported_names :: [ExportedName]
  }


data ModDetailsCompileClosure = ModDetailsCompileClosure
  { mod_det_cls_insts :: [ClsInst]
  , mod_det_tyenv :: TypeEnv
  , mod_det_exports :: [ExportedName]
  }


data CgGutsCompileClosure = CgGutsCompileClosure
  { cg_mod_name :: Maybe String
  , cg_bindings :: [CoreBind]
  , cg_breaks :: Maybe ModBreaks
  , cg_tycons :: [TyCon]
  } 


data ModDetailsClosure = ModDetailsClosure
  { mdcc_cls_insts :: [ClsInst]
  , mdcc_type_env :: TypeEnv
  , mdcc_exports :: [ExportedName]
  }

data CgGutsClosure = CgGutsClosure
  { cgcc_mod_name :: Maybe String
  , cgcc_binds :: [CoreBind]
  , cgcc_breaks :: Maybe ModBreaks
  , cgcc_tycons :: [TyCon]
  }

data ExtractedG2 = ExtractedG2
  { exg2_binds :: [(G2.Id, G2.Expr)]
  , exg2_tycons :: [G2.ProgramType]
  , exg2_classes :: [(G2.Name, G2.Id, [G2.Id])]
  , exg2_exports :: [ExportedName]
  }

emptyExtractedG2 :: ExtractedG2
emptyExtractedG2 =
  ExtractedG2
    { exg2_binds = []
    , exg2_tycons = []
    , exg2_classes = []
    , exg2_exports = [] }


