{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Interface.OutputTypes ( ExecRes (..)) where

import G2.Language

-- | A fully executed State
data ExecRes t = ExecRes { final_state :: State t
                         , conc_args :: [Expr]
                         , conc_out :: Expr
                         , violated :: Maybe FuncCall -- ^ A violated assertion
                         } deriving (Show, Read)

instance Named t => Named (ExecRes t) where
    names (ExecRes { final_state = s
                   , conc_args = es
                   , conc_out = r
                   , violated = fc }) =
                      names s <> names es <> names r <> names fc

    rename old new (ExecRes { final_state = s
                            , conc_args = es
                            , conc_out = r
                            , violated = fc }) =
      ExecRes { final_state = rename old new s
              , conc_args = rename old new es
              , conc_out = rename old new r
              , violated = rename old new fc}

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
                , violated = modifyContainedASTs f fc}

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
