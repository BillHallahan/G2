{-# LANGUAGE OverloadedStrings #-}

module G2.Execution.DataConPCMap ( DCArgBind (..)
                                 , DataConPCInfo (..)
                                 , dcpcMap
                                 , applyDCPC
                                 ) where

import G2.Language.Naming
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.Typing as T

import Data.List
import qualified Data.HashMap.Lazy as HM

import Control.Exception

data DCArgBind =
      -- | A new symbolic argument
      ArgSymb { binder_name :: Name }
      -- | A new concrete argument
    | ArgConcretize 
        { binder_name :: Name
        , fresh_vars :: [Id] -- ^ New symbolic variables to introduce, used in the Expr
        , arg_expr :: Expr -- ^ Instantiation of the argument
        }

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

-- | Map Name's of DataCons to associations of type arguments to DataConPCInfos
-- alongside an Expr representing the entire expression (used by IntToString)
dcpcMap :: TyVarEnv -> KnownValues -> TypeEnv -> HM.HashMap Name [([Type], DataConPCInfo)]
dcpcMap tv kv tenv = HM.fromList [
                      ( KV.dcCons kv, [ ([T.tyChar kv], strCons tv kv tenv) ])
                    , ( KV.dcEmpty kv, [ ([T.tyChar kv], strEmpty tv kv) ])
                  ]

strCons :: TyVarEnv -> KnownValues -> TypeEnv -> DataConPCInfo
strCons tv kv tenv = let
                        hn = Name "h" Nothing 0 ProvOther
                        tn = Name "t" Nothing 0 ProvOther
                        ti = Id tn (TyApp (T.tyList kv) (T.tyChar kv))
                        cn = Name "c" Nothing 0 ProvOther
                        ci = Id cn TyLitChar
                        asn = Name "as" Nothing 0 ProvOther
                        asi = Id asn (TyApp (T.tyList kv) (T.tyChar kv))
                        dc_char = App (mkDCChar kv tenv) (Var ci)
                        dcpc = DCPC { dc_as_pattern = asn
                                    , dc_args = [ArgConcretize { binder_name = hn
                                                            , fresh_vars = [ ci ]
                                                            , arg_expr = dc_char
                                                            }
                                                , ArgSymb tn]
                                    , dc_pc = [ExtCond (mkEqExpr tv kv
                                                    (App (App (mkStringAppend kv) (Var ci)) (Var ti))
                                                    (Var asi)) True]
                                    , dc_bindee_exprs = [dc_char, (Var ti)]
                                    }
                      in
                      dcpc

strEmpty :: TyVarEnv -> KnownValues -> DataConPCInfo
strEmpty tv kv = let
                asn = Name "as" Nothing 0 ProvOther
                asi = Id asn (TyApp (T.tyList kv) (T.tyChar kv))
                dcpc = DCPC { dc_as_pattern = asn
                            , dc_args = []
                            , dc_pc = [ExtCond (mkEqExpr tv kv
                                (App (mkStringLen kv) (Var asi))
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
