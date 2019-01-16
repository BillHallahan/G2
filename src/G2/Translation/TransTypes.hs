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


emptyModGutsClosure :: ModGutsClosure
emptyModGutsClosure =
  ModGutsClosure
    { mgcc_mod_name = Nothing
    , mgcc_binds = []
    , mgcc_tycons = []
    , mgcc_breaks = Nothing
    , mgcc_cls_insts = []
    , mgcc_type_env = emptyTypeEnv
    , mgcc_exports = []
    }

emptyModDetailsClosure :: ModDetailsClosure
emptyModDetailsClosure =
  ModDetailsClosure
    { mdcc_cls_insts = []
    , mdcc_type_env = emptyTypeEnv
    , mdcc_exports = []
    }

emptyCgGutsClosure :: CgGutsClosure
emptyCgGutsClosure =
  CgGutsClosure
    { cgcc_mod_name = Nothing
    , cgcc_binds = []
    , cgcc_breaks = Nothing
    , cgcc_tycons = []
    }


data ExtractedG2 = ExtractedG2
  { exg2_mod_names :: [T.Text]
  , exg2_binds :: [(G2.Id, G2.Expr)]
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


