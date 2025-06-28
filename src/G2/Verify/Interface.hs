module G2.Verify.Interface ( VerifyResult (..)
                           , verifyFromFile) where

import G2.Config
import G2.Initialization.MkCurrExpr
import G2.Interface
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Translation

import Control.Exception

data VerifyResult t = Verified
                    | Counterexample [ExecRes t]
                    | VerifyTimeOut
                    deriving (Show, Read)

wrapCurrExpr :: NameGen -> State t -> (State t, NameGen)
wrapCurrExpr ng s@(State { curr_expr = CurrExpr er e, type_env = tenv, known_values = kv }) =
  let
    t = tyBool kv
    (binder, ng') = freshName ng
    
    true_dc = mkDCTrue kv tenv 
    false_dc = mkDCFalse kv tenv
    true_e = mkTrue kv
    false_e = mkFalse kv
    -- Introducing a case split (1) allows us to discard branches that just lead to true, without bothering
    -- to solve NRPCs and (2) ensures that we will search for a path that leads to false when solving NRPCs
    e' = Case e (Id binder t) t [ Alt (DataAlt true_dc []) (Assume Nothing false_e true_e)
                                , Alt (DataAlt false_dc []) false_e]
  in
  (s { curr_expr = CurrExpr er e' }, ng')

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


    (init_state, entry_f, bindings, mb_modname) <- initialStateFromFile proj src
                                    Nothing False f (mkCurrExpr Nothing Nothing) mkArgTys
                                    transConfig config
    let (init_state', ng) = wrapCurrExpr (name_gen bindings) init_state
        bindings' = bindings { name_gen = ng }

    (er, b, to) <- runG2WithConfig (idName entry_f) mb_modname init_state' config' bindings'
    
    let res = case to of
                TimedOut -> VerifyTimeOut
                NoTimeOut | false_er <- filter (isFalse . final_state) er
                          , not (null false_er) -> Counterexample false_er
                          | otherwise -> assert (all (isTrue . final_state) er) Verified
    return (res, b, entry_f)
    where
        isFalse s | E.deepLookupExpr (getExpr s) (expr_env s) == Just (mkFalse (known_values s ) )= True
                  | otherwise = False

        isTrue s | E.deepLookupExpr (getExpr s) (expr_env s) == Just (mkTrue (known_values s)) = True
                 | otherwise = False