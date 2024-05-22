{-# LANGUAGE OverloadedStrings #-}

module G2.Initialization.Handles (mkHandles) where

import G2.Language
import qualified G2.Language.ExprEnv as E

mkHandles :: ExprEnv -> KnownValues -> NameGen -> (ExprEnv, [Handle], NameGen)
mkHandles eenv kv ng =
    let
        list_ty = tyList kv
        char_ty = tyChar kv
        str_ty = TyApp list_ty char_ty

        (stdin_id, ng') = freshSeededId (Name "stdin" Nothing 0 Nothing) str_ty ng
        stdin = Handle { h_filepath = "stdin"
                       , h_input = HBuffer stdin_id
                       , h_output = NoBuffer
                       , h_status = HOpen }

        (stdout_id, ng'') = freshSeededId (Name "stdout" Nothing 0 Nothing) str_ty ng'
        stdout = Handle { h_filepath = "stdout"
                        , h_input = NoBuffer
                        , h_output = HBuffer stdout_id
                        , h_status = HOpen }
        
        eenv' = E.insertSymbolic stdin_id $ E.insertSymbolic stdout_id eenv
    in
    (eenv', [stdin, stdout], ng'')