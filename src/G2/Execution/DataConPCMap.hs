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
    }

-- | Map Name's of DataCons to associations of type arguments to DataConPCInfos
dcpcMap :: KnownValues -> TypeEnv -> HM.HashMap Name [([Type], DataConPCInfo)]
dcpcMap kv tenv = HM.fromList [
                      ( KV.dcCons kv, [ ([T.tyChar kv], strConsDcpc kv tenv) ])
                    , ( KV.dcEmpty kv, [ ([T.tyChar kv], strEmptyDcpc kv) ])
                  ]

strConsDcpc :: KnownValues -> TypeEnv -> DataConPCInfo
strConsDcpc kv tenv = let
                        hn = Name "h" Nothing 0 Nothing
                        hi = Id hn (T.tyChar kv)
                        tn = Name "t" Nothing 0 Nothing
                        ti = Id tn (TyApp (T.tyList kv) (T.tyChar kv))
                        cn = Name "c" Nothing 0 Nothing
                        ci = Id cn TyLitChar
                        asn = Name "as" Nothing 0 Nothing
                        asi = Id asn (TyApp (T.tyList kv) (T.tyChar kv))
                        dcpc = DCPC { dc_as_pattern = asn
                                    , dc_args = [ArgConcretize { binder_name = hn
                                                            , fresh_vars = [ ci ]
                                                            , arg_expr = App (mkDCChar kv tenv) (Var ci)
                                                            }
                                                , ArgSymb tn]    
                                    , dc_pc = [ExtCond (mkEqExpr kv
                                                    (App (App (mkStringAppend kv) (Var ci)) (Var ti))
                                                    (Var asi)) True] }
                      in
                      dcpc

strEmptyDcpc :: KnownValues -> DataConPCInfo
strEmptyDcpc kv = let
                    asn = Name "as" Nothing 0 Nothing
                    asi = Id asn (TyApp (T.tyList kv) (T.tyChar kv))
                    dcpc = DCPC { dc_as_pattern = asn
                                , dc_args = []
                                , dc_pc = [ExtCond (mkEqExpr kv
                                    (App (mkStringLen kv) (Var asi))
                                    (Lit (LitInt 0)))
                                    True] }
                  in
                  dcpc

applyDCPC :: NameGen
          -> ExprEnv
          -> [Id] -- ^ Newly generated arguments for the data constructor
          -> Name -- ^ As pattern name to replace
          -> DataConPCInfo
          -> (ExprEnv, [PathCond], NameGen)
applyDCPC ng eenv new_ids prev_asp (DCPC { dc_as_pattern = asp, dc_args = ars, dc_pc = pc }) =
    let
        (ng', eenv', pc') = foldl' mkDCArg (ng, eenv, pc) (zip ars new_ids)
        pc'' = rename asp prev_asp pc'
    in
    assert (length ars == length new_ids)
    (eenv', pc'', ng')


mkDCArg :: (NameGen, ExprEnv, [PathCond]) -> (DCArgBind, Id) -> (NameGen, ExprEnv, [PathCond])
mkDCArg (ng, eenv, pc) (ArgSymb bi, i) =
    let
        eenv' = E.insertSymbolic i eenv
        pc' = rename bi (idName i) pc
    in
    (ng, eenv', pc')
mkDCArg (ng, eenv, pc) (ArgConcretize { binder_name = bn, fresh_vars = fv, arg_expr = e}, i) =
    let
        (fv', ng') = freshSeededIds fv ng
        rn_hm = HM.fromList $ (bn, idName i):zip (map idName fv) (map idName fv')
        e' = renames rn_hm e
        pc' = renames rn_hm pc
        eenv' = E.insert (idName i) e' $ foldl' (flip E.insertSymbolic) eenv fv'
    in
    (ng', eenv', pc')
