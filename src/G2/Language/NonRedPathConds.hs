{-# LANGUAGE BangPatterns, DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, OverloadedStrings, PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE InstanceSigs #-}

module G2.Language.NonRedPathConds ( Focus
                                   , GenFocus (..)
                                   , NonRedPathConds
                                   , NRPC
                                   , emptyNRPC
                                   , emptyNRPCNonUniq
                                   , addNRPC
                                   , addFirstNRPC
                                   , getNRPC
                                   , getLastNRPC
                                   , nullNRPC
                                   , toListNRPC
                                   , pattern (:*>)
                                   , pattern (:<*)
                                   , getNRPCUnique
                                   , setFocus
                                   , allNRPC ) where

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax
import qualified G2.Language.ExprEnv as E

import Data.Data
import qualified Data.Foldable as F
import Data.Hashable
import Data.Sequence
import GHC.Generics
import G2.Language.ExprEnv (deepLookupVar)

type NRPC = (Focus, Expr, Expr)
data NonRedPathConds = NRPCs { nrpcs :: Seq NRPC, nrpc_uniq :: Unique }
                          deriving (Eq, Read, Show, Data, Generic, Typeable)

instance Hashable NonRedPathConds

-- Note [NRPC Focus]
-- `Focus` allows for the verifier (Nova) to track NRPCs that we know must be evaluated, versus NRPCs that may or may
-- not be required to evaluated.  This matters so that we know if we are making progress in reducing the state.
-- Reducing a focused NRPC is definitely forwarding the states evaluation. Reducing an unfocused NRPC might be helpful
-- to make approximation work out, but is not actually guaranteed to be forwarding evaluation of the state.
--
-- The `Focused` constructor means that we know the expressions must be evaluated and terminate for the states to terminate.
-- `Unfocused` means there may be some execution paths that do not require evaluating the NRPC expressions.
--
-- Suppose we have the expression:
-- @
--   f (g a) (h b)
-- @
-- where the function f is defined as:
-- @
--   f x y = case y of
--              [] -> e1 
--              _:_ -> x
-- @
-- The expression `f (g a) (h b)` must be evaluated, and so could be added as a focused NRPC.
-- NRPCs for `g a` or `h b` could also be introduced, but only as unfocused NRPCs, because there might be code
-- paths that do not evaluate these calls to `g` or `h`.  If we introduce all these NRPCs, we would get the expression:
-- @
--    sym_f
-- @
-- with NRPCs:
-- @
-- f sym_g sym_h = sym_f, focused 
-- g a = sym_g, unfocused 
-- h b = sym_h, unfocused 
-- @
--
-- There are two further concerns:
-- (1) Suppose that we go to solve the NRPC for sym_f, and thus evaluate:
-- @
--     f sym_g sym_h
-- @
-- which reduces to:
-- @
--   case sym_h of
--        [] -> e1 
--         _:_ -> sym_g
-- @
-- The evaluator now knows that `sym_h` (and thus, `h b`) must be evaluated. We can thus change the NRPC `h b = sym_h`
-- from `unfocused` to `focused`. Further, if we have already done any reduction on `h b`, any NRPCs introduced
-- that had there symbolic variable evaluated during running `h b` should also be set to focused.  Thus, we track a
-- mapping of which unfocused symbiolic variables have forced other unfocused symbolic variables to be run.  All this
-- behavior is implemented as part of the `adjustFocusReducer` in "G2.Verify.Reducer".
--
-- (2) If we reduce a state's expression to False and have only unfocused NRPCs, then those unfocused NRPCs are not actually
-- required to fully reduce the state.  If they were, they would have been switched to focused NRPCs by the `adjustFocusReducer`.
-- As such, the `adjustFocusReducer` also wipes out the NRPCs if the state's expression is false and all are unfocused. 


-- | Is evaluation of the NRPC being forced? I.e. does evaluation of the state definitely evaluate the NRPC expression(s).
-- See Note [NRPC Focus] and `Focus`.
data GenFocus n = Focused
                | Unfocused n
                deriving (Eq, Read, Show, Data, Generic, Typeable)

-- | The Name is used to track the symbolic variable introduced by the NRPC.
type Focus = GenFocus Name

instance Hashable n => Hashable (GenFocus n)

emptyNRPC :: NameGen -> (NonRedPathConds, NameGen)
emptyNRPC ng = let (uniq, ng') = freshUnique ng in (NRPCs Empty uniq, ng')

emptyNRPCNonUniq :: NonRedPathConds
emptyNRPCNonUniq = NRPCs Empty 0

addNRPC :: NameGen -> Focus -> Expr -> Expr -> NonRedPathConds -> (NameGen, NonRedPathConds)
addNRPC ng focus e1 e2 (NRPCs nrpc curr_uniq) =
    let
        (e1', e2') = varOnRight e1 e2
        (uniq, ng') = if focus == Focused then freshUnique ng else (curr_uniq, ng)
    in
    (ng', NRPCs (nrpc :|> (focus, e1', e2')) uniq)

addFirstNRPC :: NameGen -> Focus -> Expr -> Expr -> NonRedPathConds -> (NameGen, NonRedPathConds)
addFirstNRPC ng focus e1 e2 (NRPCs nrpc curr_uniq) =
    let
        (e1', e2') = varOnRight e1 e2
        (uniq, ng') = if focus == Focused then freshUnique ng else (curr_uniq, ng)
    in
    (ng', NRPCs ((focus, e1', e2') :<| nrpc) uniq)

varOnRight :: Expr -> Expr -> (Expr, Expr)
varOnRight e1@(Var _) e2 = (e2, e1)
varOnRight e1@(Tick _ (Var _)) e2 = (e2, e1)
varOnRight e1 e2 = (e1, e2)

getNRPC :: NonRedPathConds -> Maybe (NRPC, NonRedPathConds)
getNRPC (NRPCs Empty _) = Nothing
getNRPC (NRPCs ((focus, e1, e2) :<| nrpc) uniq) = Just ((focus, e1, e2), NRPCs nrpc uniq)

getLastNRPC :: NonRedPathConds -> Maybe (NRPC, NonRedPathConds)
getLastNRPC (NRPCs Empty _) = Nothing
getLastNRPC (NRPCs (nrpc :|> (focus, e1, e2)) uniq) = Just ((focus, e1, e2), NRPCs nrpc uniq)

nullNRPC :: NonRedPathConds -> Bool
nullNRPC (NRPCs Empty _) = True
nullNRPC _ = False

toListNRPC :: NonRedPathConds -> [NRPC]
toListNRPC = F.toList . nrpcs

getNRPCUnique :: NonRedPathConds -> Unique
getNRPCUnique = nrpc_uniq

setFocus :: Name -> Focus -> E.ExprEnv -> NonRedPathConds -> NonRedPathConds
setFocus n focus eenv (NRPCs nrpc uniq) = NRPCs (fmap set nrpc) uniq
    where
        set (_, e1, e2@(Var (Id n' _))) | areSame n' = (focus, e1, e2)
        set e1_e2 = e1_e2

        areSame n' = deepLookupVar n eenv == deepLookupVar n' eenv

allNRPC :: (NRPC -> Bool) -> NonRedPathConds -> Bool
allNRPC p (NRPCs nrpc _) = all p nrpc

pattern (:*>) :: NRPC -> NonRedPathConds -> NonRedPathConds
pattern e1_e2 :*> nrpc <- (getNRPC -> Just (e1_e2, nrpc))

pattern (:<*) :: NonRedPathConds -> NRPC -> NonRedPathConds
pattern nrpc :<* e1_e2 <- (getLastNRPC -> Just (e1_e2, nrpc))

instance ASTContainer (GenFocus n) Expr where
    containedASTs _ = []
    modifyContainedASTs _ focus = focus

instance ASTContainer (GenFocus n) Type where
    containedASTs _ = []
    modifyContainedASTs _ focus = focus

instance Named n => Named (GenFocus n) where
    names (Unfocused n) = names n
    names _ = Empty
    
    rename old new (Unfocused n) = Unfocused $ rename old new n
    rename _ _ focus = focus

    renames hm (Unfocused n) = Unfocused $ renames hm n
    renames _ focus = focus

instance ASTContainer NonRedPathConds Expr where
    containedASTs = containedASTs . nrpcs
    modifyContainedASTs f (NRPCs nrpc uniq) = NRPCs { nrpcs = modifyContainedASTs f nrpc, nrpc_uniq = uniq } 

instance ASTContainer NonRedPathConds Type where
    containedASTs = containedASTs . nrpcs
    modifyContainedASTs f (NRPCs nrpc uniq) = NRPCs { nrpcs = modifyContainedASTs f nrpc, nrpc_uniq = uniq } 

instance Named NonRedPathConds where
    names (NRPCs nrpc _) = names nrpc
    rename old new (NRPCs nrpc uniq) = NRPCs (rename old new nrpc) uniq
    renames hm (NRPCs nrpc uniq) = NRPCs (renames hm nrpc) uniq