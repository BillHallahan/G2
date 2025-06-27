module G2.Verify.Interface ( VerifyResult (..)
                           , verifyFromFile) where

import G2.Config
import G2.Interface
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Translation

import Control.Exception

data VerifyResult t = Verified
                    | Counterexample [ExecRes t]
                    | VerifyTimeOut
                    deriving (Show, Read)

verifyFromFile :: [FilePath]
               -> [FilePath]
               -> StartFunc
               -> TranslationConfig
               -> Config
               -> IO (VerifyResult (), Bindings, Id)
verifyFromFile proj src f transConfig config = do
    let config' = config {
                         -- For soundness, we must exhaustively search all states that are not discarded via approximation,
                         -- so we disable the step count.
                           step_limit = False
                         -- For soundness, cannot limit number of outputs explored 
                         , maxOutputs = Nothing
                         -- Not using hpc ticks
                         , hpc_discard_strat = False
                         -- Use approximation to add repeated function calls to NRPCs
                         , approx_nrpc = Nrpc
                         -- Use approximation to discard states that are approximated by previously explored states
                         , approx_discard = True }

    (er, b, to, entry_f) <- runG2FromFile proj src Nothing Nothing Nothing False f transConfig config'
    
    let res = case to of
                TimedOut -> VerifyTimeOut
                NoTimeOut | false_er <- filter (isFalse . final_state) er
                          , not (null false_er) -> Counterexample false_er
                          | otherwise -> assert (all (isTrue . final_state) er) Verified
    return (res, b, entry_f)
    where
        isFalse s | getExpr s == mkFalse (known_values s ) = True
                  | otherwise = False

        isTrue s | E.deepLookupExpr (getExpr s) (expr_env s) == Just (mkTrue (known_values s)) = True
                 | otherwise = False