{-# LANGUAGE DeriveDataTypeable, OverloadedStrings #-}

module G2.Execution.DataConPCMap ( DCArgBind (..)
                                 , DataConPCInfo (..)
                                 , DataConPCMap
                                 -- * Constructing/using the DCPC Map
                                 , addToDCPCMap
                                 , dcpcMap
                                 , applyDCPC

                                 -- * Helpers for constructing the DCPC Map
                                 , listCons
                                 , listEmpty
                                 ) where

import G2.Language.Naming
import G2.Language.Syntax
import G2.Language.Expr
import G2.Language.ExprEnv (ExprEnv)
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues (KnownValues)
import qualified G2.Language.KnownValues as KV
import G2.Language.PathConds (PathCond (..))
import G2.Language.Primitives
import G2.Language.TypeEnv (TypeEnv)
import qualified G2.Language.Typing as T
import G2.Language.TyVarEnv (TyVarEnv)

import Data.List
import qualified Data.HashMap.Lazy as HM

import Control.Exception
import Data.Data (Data, Typeable)

data DCArgBind =
      -- | A new symbolic argument
      ArgSymb { binder_name :: Name }
      -- | A new concrete argument
    | ArgConcretize 
        { binder_name :: Name
        , fresh_vars :: [Id] -- ^ New symbolic variables to introduce, used in the Expr
        , arg_expr :: Expr -- ^ Instantiation of the argument
        }
    deriving (Show, Eq, Read, Typeable, Data)

-- | When adding a data constructor, we can also add path constraints, to enable
-- reasoning via the SMT solver.  For example, Strings can be manipulated via concretization,
-- but also SMT solvers include support for certain String primitives.  So we both concretize
-- (to run arbitrary Haskell functions) but add to the path constraints to enable SMT solver
-- reasoning when possible.
--
-- This type ties specific data constructors to path constraints that should be added during concretization.
-- The path constraints are written over the dc_args, which are either newly introduced symbolic variables
-- or newly introduced concrete values.
data DataConPCInfo =
    DCPC
    { dc_as_pattern :: Name -- ^ The entirety of the data constructor application
    , dc_args :: [DCArgBind] -- ^ How to instantiate arguments for the DCPC
    , dc_pc :: [PathCond] -- ^ Path constraints to generate, written over the DCPC
    , dc_bindee_exprs :: [Expr] -- ^ Expressions corresponding to the args
    }
    deriving (Show, Eq, Read, Typeable, Data)

type DataConPCMap = HM.HashMap Name [([Type], DataConPCInfo)]

addToDCPCMap :: Name -> [Type] -> DataConPCInfo -> DataConPCMap -> DataConPCMap
addToDCPCMap n ts dcpi = HM.insertWith (++) n [(ts, dcpi)]

-- | Map Name's of DataCons to associations of type arguments to DataConPCInfos
-- alongside an Expr representing the entire expression (used by IntToString)
dcpcMap :: TyVarEnv -> KnownValues -> TypeEnv -> HM.HashMap Name [([Type], DataConPCInfo)]
dcpcMap tv kv tenv = HM.fromList [
                      ( KV.dcCons kv, [ ([T.tyChar kv], strCons kv tenv tv) ])
                    , ( KV.dcEmpty kv, [ ([T.tyChar kv], strEmpty kv tv) ])
                  ]

strCons :: KnownValues -> TypeEnv -> TyVarEnv -> DataConPCInfo
strCons kv tenv = listCons' id (mkDCChar kv tenv) (T.tyChar kv) kv

listCons :: Expr -> Type -> KnownValues -> TyVarEnv -> DataConPCInfo
listCons = listCons' (App (Prim SeqUnit TyUnknown))

listCons' :: (Expr -> Expr) -> Expr -> Type -> KnownValues -> TyVarEnv -> DataConPCInfo
listCons' f dc t kv tv = let
                        hn = Name "h" Nothing 0 Nothing
                        tn = Name "t" Nothing 0 Nothing
                        ti = Id tn (TyApp (T.tyList kv) (T.returnType $ T.typeOf tv dc))
                        cn = Name "c" Nothing 0 Nothing
                        ci = Id cn t
                        asn = Name "as" Nothing 0 Nothing
                        asi = Id asn (TyApp (T.tyList kv) (T.returnType $ T.typeOf tv dc))
                        dc_e = App dc (Var ci)
                        dcpc = DCPC { dc_as_pattern = asn
                                    , dc_args = [ArgConcretize { binder_name = hn
                                                               , fresh_vars = [ ci ]
                                                               , arg_expr = dc_e
                                                            }
                                                , ArgSymb tn]
                                    , dc_pc = [ExtCond (mkEqExpr tv kv
                                                    (App (App (mkSeqAppend t kv) (f (Var ci))) (Var ti))
                                                    (Var asi)) True]
                                    , dc_bindee_exprs = [dc_e, (Var ti)]
                                    }
                      in
                      dcpc

strEmpty :: KnownValues -> TyVarEnv -> DataConPCInfo
strEmpty kv = listEmpty (T.tyChar kv) kv

listEmpty :: Type -> KnownValues -> TyVarEnv -> DataConPCInfo
listEmpty t kv tv = let
                asn = Name "as" Nothing 0 Nothing
                asi = Id asn (TyApp (T.tyList kv) t)
                dcpc = DCPC { dc_as_pattern = asn
                            , dc_args = []
                            , dc_pc = [ExtCond (mkEqExpr tv kv
                                (App (mkSeqLen t kv) (Var asi))
                                (Lit (LitInt 0))) True]
                            , dc_bindee_exprs = []
                            }
              in
              dcpc

applyDCPC :: NameGen
          -> ExprEnv
          -> [Id] -- ^ Newly generated arguments for the data constructor
          -> Expr -- ^ Expr to replace as pattern name with
          -> DataConPCInfo
          -> (ExprEnv, [PathCond], NameGen, [Expr])
applyDCPC ng eenv new_ids as_expr (DCPC { dc_as_pattern = as_p, dc_args = ars, dc_pc = pc, dc_bindee_exprs = be }) =
    let
        (ng', eenv', pc', be') = foldl' mkDCArg (ng, eenv, pc, be) (zip ars new_ids)
        -- Replace expr corresponding to as pattern in PathCond list
        pc'' = replaceVar as_p as_expr pc'
    in
    assert (length ars == length new_ids)
    (eenv', pc'', ng', be')

mkDCArg :: (NameGen, ExprEnv, [PathCond], [Expr]) -> (DCArgBind, Id) -> (NameGen, ExprEnv, [PathCond], [Expr])
mkDCArg (ng, eenv, pc, be) (ArgSymb bi, i) =
    let
        eenv' = E.insertSymbolic i eenv
        pc' = rename bi (idName i) pc
        be' = map (rename bi (idName i)) be
    in
    (ng, eenv', pc', be')
mkDCArg (ng, eenv, pc, be) (ArgConcretize { binder_name = bn, fresh_vars = fv, arg_expr = e}, i) =
    let
        (fv', ng') = freshSeededIds fv ng
        rn_hm = HM.fromList $ (bn, idName i):zip (map idName fv) (map idName fv')
        e' = renames rn_hm e
        pc' = renames rn_hm pc
        be' = map (renames rn_hm) be
        eenv' = E.insert (idName i) e' $ foldl' (flip E.insertSymbolic) eenv fv'
    in
    (ng', eenv', pc', be')
