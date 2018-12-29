{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Interface.OutputTypes ( ExecOut (..)
                                , ExecRes (..)) where

import G2.Language

data ExecOut t = ExecOut { exec_res :: [ExecRes t] -- ^ Fully executed states
                         , in_progress :: [State t] -- ^ States that were generated but not fully executed
                         }

-- | A fully executed State
data ExecRes t = ExecRes { final_state :: State t
                         , conc_args :: [Expr]
                         , conc_out :: Expr
                         , violated :: Maybe FuncCall -- ^ A violated assertion
                         } deriving (Show, Read)

instance Named t => Named (ExecOut t) where
    names (ExecOut { exec_res = er, in_progress = ip }) =
        names er ++ names ip

    rename old new (ExecOut { exec_res = er, in_progress = ip }) =
        ExecOut { exec_res = rename old new er, in_progress = rename old new ip }

    renames hm (ExecOut { exec_res = er, in_progress = ip }) =
        ExecOut { exec_res = renames hm er, in_progress = renames hm ip }

instance ASTContainer t Expr => ASTContainer (ExecOut t) Expr where
    containedASTs (ExecOut { exec_res = er, in_progress = ip }) =
        containedASTs er ++ containedASTs ip

    modifyContainedASTs f (ExecOut { exec_res = er, in_progress = ip }) =
        ExecOut { exec_res = modifyContainedASTs f er
                , in_progress = modifyContainedASTs f ip }

instance ASTContainer t Type => ASTContainer (ExecOut t) Type where
    containedASTs (ExecOut { exec_res = er, in_progress = ip }) =
        containedASTs er ++ containedASTs ip

    modifyContainedASTs f (ExecOut { exec_res = er, in_progress = ip }) =
        ExecOut { exec_res = modifyContainedASTs f er
                , in_progress = modifyContainedASTs f ip }

instance Named t => Named (ExecRes t) where
    names (ExecRes { final_state = s
                   , conc_args = es
                   , conc_out = r
                   , violated = fc }) =
                      names s ++ names es ++ names r ++ names fc

    rename old new (ExecRes { final_state = s
                            , conc_args = es
                            , conc_out = r
                            , violated = fc }) =
      ExecRes { final_state = rename old new s
              , conc_args = rename old new es
              , conc_out = rename old new r
              , violated = rename old new fc }

    renames hm (ExecRes { final_state = s
                        , conc_args = es
                        , conc_out = r
                        , violated = fc }) =
      ExecRes { final_state = renames hm s
              , conc_args = renames hm es
              , conc_out = renames hm r
              , violated = renames hm fc }

instance ASTContainer t Expr => ASTContainer (ExecRes t) Expr where
    containedASTs (ExecRes { final_state = s
                           , conc_args = es
                           , conc_out = r
                           , violated = fc }) =
      containedASTs s ++ containedASTs es ++ containedASTs r ++ containedASTs fc

    modifyContainedASTs f (ExecRes { final_state = s
                                   , conc_args = es
                                   , conc_out = r
                                   , violated = fc }) =
        ExecRes { final_state = modifyContainedASTs f s
                , conc_args = modifyContainedASTs f es
                , conc_out = modifyContainedASTs f r
                , violated = modifyContainedASTs f fc }

instance ASTContainer t Type => ASTContainer (ExecRes t) Type where
    containedASTs (ExecRes { final_state = s
                           , conc_args = es
                           , conc_out = r
                           , violated = fc }) =
      containedASTs s ++ containedASTs es ++ containedASTs r ++ containedASTs fc

    modifyContainedASTs f (ExecRes { final_state = s
                                   , conc_args = es
                                   , conc_out = r
                                   , violated = fc }) =
        ExecRes { final_state = modifyContainedASTs f s
                , conc_args = modifyContainedASTs f es
                , conc_out = modifyContainedASTs f r
                , violated = modifyContainedASTs f fc }
