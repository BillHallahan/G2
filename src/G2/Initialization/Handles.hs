{-# LANGUAGE OverloadedStrings #-}

module G2.Initialization.Handles (mkHandles) where

import qualified Data.HashMap.Lazy as HM

import G2.Language
import qualified G2.Language.ExprEnv as E

mkHandles :: ExprEnv -> KnownValues -> NameGen -> (ExprEnv, HM.HashMap Name Handle, NameGen)
mkHandles eenv kv ng =
    let
        list_ty = tyList kv
        char_ty = tyChar kv
        str_ty = TyApp list_ty char_ty

        (stdin_id, ng') = freshSeededId (Name "stdin" Nothing 0 Nothing) str_ty ng
        stdin = HandleInfo { h_filepath = "stdin"
                           , h_start = stdin_id
                           , h_pos = stdin_id
                           , h_status = HOpen }

        (stdout_id, ng'') = freshSeededId (Name "stdout" Nothing 0 Nothing) str_ty ng'
        stdout = HandleInfo { h_filepath = "stdout"
                            , h_start = stdout_id
                            , h_pos = stdout_id
                            , h_status = HOpen }
        
        eenv' = E.insertSymbolic stdin_id $ E.insertSymbolic stdout_id eenv
    in
    (eenv', HM.fromList [(undefined, stdin), (undefined, stdout)], ng'')