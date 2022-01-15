{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}

module G2.Equiv.Types ( module G2.Equiv.Types
                      , module G2.Equiv.G2Calls) where

import G2.Equiv.G2Calls
import G2.Language

import GHC.Generics (Generic)
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
  names (Unresolved s_pair) = names s_pair
  rename old new m = case m of
    Induction im -> Induction $ rename old new im
    Coinduction cm -> Coinduction $ rename old new cm
    Equality em -> Equality $ rename old new em
    NoObligations s_pair -> NoObligations $ rename old new s_pair
    NotEquivalent s_pair -> NotEquivalent $ rename old new s_pair
    SolverFail s_pair -> SolverFail $ rename old new s_pair
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
-- cycle_term is the SWHNF state on the other side
data CycleMarker = CycleMarker {
    cycle_real_present :: (StateET, StateET)
  , cycle_past :: StateET
  , cycle_term :: StateET
  , cycle_mapping :: HM.HashMap Id Expr
  , cycle_side :: Side
}

instance Named CycleMarker where
  names (CycleMarker (s1, s2) p q _ _) =
    names s1 DS.>< names s2 DS.>< names p DS.>< names q
  rename old new (CycleMarker (s1, s2) p q hm sd) =
    let r = rename old new
        s1' = r s1
        s2' = r s2
        p' = r p
        q' = r q
    in CycleMarker (s1', s2') p' q' hm sd

data Lemma = Lemma { lemma_name :: String
                   , lemma_lhs :: StateET
                   , lemma_rhs :: StateET
                   , lemma_lhs_origin :: String
                   , lemma_rhs_origin :: String
                   , lemma_to_be_proven :: [(StateH, StateH)] }
                   deriving (Eq, Generic)

instance Hashable Lemma

instance Named Lemma where
  names (Lemma _ s1 s2 _ _ sh) = names s1 DS.>< names s2 DS.>< names sh
  rename old new (Lemma lnm s1 s2 f1 f2 sh) =
    Lemma lnm (rename old new s1) (rename old new s2) f1 f2 (rename old new sh)

type ProposedLemma = Lemma
type ProvenLemma = Lemma
type DisprovenLemma = Lemma
