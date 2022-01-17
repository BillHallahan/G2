{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}

module G2.Equiv.Types ( module G2.Equiv.Types
                      , module G2.Equiv.G2Calls) where

import G2.Equiv.G2Calls
import G2.Execution.Reducer
import G2.Language
import qualified G2.Language.ExprEnv as E

import GHC.Generics (Generic)
import Control.Exception
import Data.Data (Typeable)
import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.Sequence as DS

data StateH = StateH {
      latest :: StateET
    , history :: [StateET]
    , inductions :: [IndMarker]
    , discharge :: Maybe StateET
  }
  deriving (Eq, Generic)

instance Hashable StateH

instance Named StateH where
  names (StateH s h ims d) =
    names s DS.>< names h DS.>< names ims DS.>< names d
  rename old new (StateH s h ims d) =
    StateH (rename old new s) (rename old new h) (rename old new ims) (rename old new d)

newStateH :: StateET -> StateH
newStateH s = StateH {
    latest = s
  , history = []
  , inductions = []
  , discharge = Nothing
  }

-- The container field is only relevant for induction.  When the expression for
-- one past state is actually an inner scrutinee of an expression that really
-- was encountered in the past, the container holds the full expression.
data PrevMatch t = PrevMatch {
    present :: (State t, State t)
  , past :: (State t, State t)
  , conditions :: (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
  , container :: State t
}

-- TODO new constructor for lemma proving
-- also have one for lemma application
data ActMarker = Induction IndMarker
               | Coinduction CoMarker
               | Equality EqualMarker
               | NoObligations (StateET, StateET)
               | NotEquivalent (StateET, StateET)
               | SolverFail (StateET, StateET)
               | CycleFound CycleMarker
               | Unresolved (StateET, StateET)

instance Named ActMarker where
  names (Induction im) = names im
  names (Coinduction cm) = names cm
  names (Equality em) = names em
  names (NoObligations s_pair) = names s_pair
  names (NotEquivalent s_pair) = names s_pair
  names (SolverFail s_pair) = names s_pair
  names (CycleFound cm) = names cm
  names (Unresolved s_pair) = names s_pair
  rename old new m = case m of
    Induction im -> Induction $ rename old new im
    Coinduction cm -> Coinduction $ rename old new cm
    Equality em -> Equality $ rename old new em
    NoObligations s_pair -> NoObligations $ rename old new s_pair
    NotEquivalent s_pair -> NotEquivalent $ rename old new s_pair
    SolverFail s_pair -> SolverFail $ rename old new s_pair
    CycleFound cm -> CycleFound $ rename old new cm
    Unresolved s_pair -> Unresolved $ rename old new s_pair

data Marker = Marker (StateH, StateH) ActMarker

instance Named Marker where
  names (Marker (sh1, sh2) m) =
    names sh1 DS.>< names sh2 DS.>< names m
  rename old new (Marker (sh1, sh2) m) =
    Marker (rename old new sh1, rename old new sh2) $ rename old new m

data Side = ILeft | IRight deriving (Eq, Show, Typeable, Generic)

instance Hashable Side

data IndMarker = IndMarker {
      ind_real_present :: (StateET, StateET)
    , ind_used_present :: (StateET, StateET)
    , ind_past :: (StateET, StateET)
    , ind_result :: (StateET, StateET)
    , ind_present_scrutinees :: (Expr, Expr)
    , ind_past_scrutinees :: (StateET, StateET)
    , ind_side :: Side
    , ind_fresh_name :: Name
  }
  deriving (Eq, Generic)

instance Hashable IndMarker

-- TODO shouldn't need present scrutinees
instance Named IndMarker where
  names im =
    let (s1, s2) = ind_real_present im
        (q1, q2) = ind_used_present im
        (p1, p2) = ind_past im
        (s1', s2') = ind_result im
        (r1, r2) = ind_past_scrutinees im
        states = [s1, s2, q1, q2, p1, p2, s1', s2', r1, r2]
    in foldr (DS.><) DS.empty $ map names states
  rename old new im =
    let r = rename old new
    in im {
      ind_real_present = r $ ind_real_present im
    , ind_used_present = r $ ind_used_present im
    , ind_past = r $ ind_past im
    , ind_result = r $ ind_result im
    , ind_present_scrutinees = rename old new $ ind_present_scrutinees im
    , ind_past_scrutinees = r $ ind_past_scrutinees im
    , ind_fresh_name = rename old new $ ind_fresh_name im
    }

-- states paired with lemmas show what the state was before lemma usage
data CoMarker = CoMarker {
    co_real_present :: (StateET, StateET)
  , co_used_present :: (StateET, StateET)
  , co_past :: (StateET, StateET)
  , lemma_used_left :: Maybe (StateET, Lemma)
  , lemma_used_right :: Maybe (StateET, Lemma)
}

instance Named CoMarker where
  names (CoMarker (s1, s2) (q1, q2) (p1, p2) lemma_l lemma_r) =
    (DS.><) (names [s1, s2, q1, q2, p1, p2]) ((names lemma_l) DS.>< (names lemma_r))
  rename old new (CoMarker (s1, s2) (q1, q2) (p1, p2) lemma_l lemma_r) =
    let r = rename old new
        s1' = r s1
        s2' = r s2
        q1' = r q1
        q2' = r q2
        p1' = r p1
        p2' = r p2
        lemma_l' = rename old new lemma_l
        lemma_r' = rename old new lemma_r
    in CoMarker (s1', s2') (q1', q2') (p1', p2') lemma_l' lemma_r'

reverseCoMarker :: CoMarker -> CoMarker
reverseCoMarker (CoMarker (s1, s2) (q1, q2) (p1, p2) lemma_l lemma_r) =
  CoMarker (s2, s1) (q2, q1) (p2, p1) lemma_r lemma_l

data EqualMarker = EqualMarker {
    eq_real_present :: (StateET, StateET)
  , eq_used_present :: (StateET, StateET)
}

instance Named EqualMarker where
  names (EqualMarker (s1, s2) (q1, q2)) =
    foldr (DS.><) DS.empty $ map names [s1, s2, q1, q2]
  rename old new (EqualMarker (s1, s2) (q1, q2)) =
    let r = rename old new
        s1' = r s1
        s2' = r s2
        q1' = r q1
        q2' = r q2
    in EqualMarker (s1', s2') (q1', q2')

-- the indicated side is the one with the cycle
-- cycle_past is the past state that matches the present
data CycleMarker = CycleMarker {
    cycle_real_present :: (StateET, StateET)
  , cycle_past :: StateET
  , cycle_mapping :: HM.HashMap Id Expr
  , cycle_side :: Side
}

instance Named CycleMarker where
  names (CycleMarker (s1, s2) p _ _) =
    names s1 DS.>< names s2 DS.>< names p
  rename old new (CycleMarker (s1, s2) p hm sd) =
    let r = rename old new
        s1' = r s1
        s2' = r s2
        p' = r p
    in CycleMarker (s1', s2') p' hm sd

-- | We have two kinds of `ProposedLemma`.
-- `PropEquiv` lemmas simply aim to show that the two sides of the lemma are equivalent,
-- using our normal proof tactics.
-- `PropEvalsTo` lemmas reduce the right hand side and create a new lemma for each stopping point
-- until the RHS state branches, at which point we discard the proposed lemma.
-- Proven lemmas (the `Lemma` type) record which method they were proven by using the
-- `lemma_type` field.  Only `PropEvalsTo` lemmas may be used with coinduction.
data ProposedLemma = PropEquiv Lemma
                   | PropEvalsTo PropEvalsToLemma
                   deriving (Eq, Generic)

instance Hashable ProposedLemma

instance Named ProposedLemma where
    names (PropEquiv l) = names l
    names (PropEvalsTo pel) = names pel

    rename old new (PropEquiv l) = PropEquiv $ rename old new l
    rename old new (PropEvalsTo pel) = PropEvalsTo $ rename old new pel

data PropEvalsToLemma = PEL { et_lemma_name :: String
                            , et_lemma_lhs :: StateET
                            , et_lemma_rhs :: StateET
                            , et_lemma_origin :: String}
                            deriving (Eq, Generic)

instance Hashable PropEvalsToLemma

instance Named PropEvalsToLemma where
    names (PEL { et_lemma_lhs = lhs, et_lemma_rhs = rhs }) =
      names lhs DS.>< names rhs
    rename old new pel@(PEL { et_lemma_lhs = lhs, et_lemma_rhs = rhs }) =
        pel { et_lemma_lhs = rename old new lhs
            , et_lemma_rhs = rename old new rhs }

data LemmaType = EquivLemma | EvalsToLemma
                 deriving (Eq, Generic)

instance Hashable LemmaType

data Lemma = Lemma { lemma_name :: String
                   , lemma_lhs :: StateET
                   , lemma_rhs :: StateET
                   , lemma_lhs_origin :: String
                   , lemma_rhs_origin :: String
                   , lemma_to_be_proven :: [(StateH, StateH)]
                   , lemma_type :: LemmaType }
                   deriving (Eq, Generic)

instance Hashable Lemma

instance Named Lemma where
  names (Lemma _ s1 s2 _ _ sh _) = names s1 DS.>< names s2 DS.>< names sh
  rename old new (Lemma lnm s1 s2 f1 f2 sh lt) =
    Lemma lnm (rename old new s1) (rename old new s2) f1 f2 (rename old new sh) lt

type ProvenLemma = Lemma
type DisprovenLemma = ProposedLemma

mkPropEquivLemma :: String -> StateET -> StateET -> StateET -> StateET -> ProposedLemma
mkPropEquivLemma lm_name or_s1 or_s2 s1 s2 =
    assert (map idName (E.symbolicIds (expr_env s1)) == map idName (E.symbolicIds (expr_env s2)))
          PropEquiv $ Lemma { lemma_name = lm_name
                            , lemma_lhs = s1
                            , lemma_rhs = s2
                            , lemma_lhs_origin = folder_name . track $ or_s1
                            , lemma_rhs_origin = folder_name . track $ or_s2
                            , lemma_to_be_proven  =[(newStateH s1, newStateH s2)]
                            , lemma_type = EvalsToLemma}

mkPropEvalsToLemma :: String -> StateET -> ProposedLemma
mkPropEvalsToLemma lm_name s =
        PropEvalsTo $ PEL { et_lemma_name = lm_name
                          , et_lemma_lhs = s
                          , et_lemma_rhs = s
                          , et_lemma_origin = folder_name . track $ s }

proposedLemmaToLemma :: ProposedLemma -> Lemma
proposedLemmaToLemma (PropEquiv l) = l
proposedLemmaToLemma (PropEvalsTo pel) =
    Lemma { lemma_name = et_lemma_name pel
          , lemma_lhs = et_lemma_lhs pel
          , lemma_rhs = et_lemma_rhs pel
          , lemma_lhs_origin = et_lemma_origin pel
          , lemma_rhs_origin = et_lemma_origin pel
          , lemma_to_be_proven = []
          , lemma_type = EvalsToLemma }

isPropEquiv :: ProposedLemma -> Bool
isPropEquiv (PropEquiv _) = True
isPropEquiv _ = False

isPropEvalsTo :: ProposedLemma -> Bool
isPropEvalsTo (PropEvalsTo _) = True
isPropEvalsTo _ = False

repProposedLemmaName :: String -> ProposedLemma -> ProposedLemma
repProposedLemmaName lem_name (PropEquiv l) = PropEquiv $ l { lemma_name = lem_name }
repProposedLemmaName lem_name (PropEvalsTo l) = PropEvalsTo $ l { et_lemma_name = lem_name }

lemmaName :: ProposedLemma -> String
lemmaName (PropEquiv l) = lemma_name l
lemmaName (PropEvalsTo pel) = et_lemma_name pel

lemmaLHS :: ProposedLemma -> StateET
lemmaLHS (PropEquiv l) = lemma_lhs l
lemmaLHS (PropEvalsTo l) = et_lemma_lhs l

lemmaRHS :: ProposedLemma -> StateET
lemmaRHS (PropEquiv l) = lemma_rhs l
lemmaRHS (PropEvalsTo l) = et_lemma_rhs l
