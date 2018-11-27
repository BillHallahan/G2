module G2.Language.Located ( Located (..)
                                     , Spanning (..)
                                     , Locatable (..)
                                     , Spannable (..)
                                     , topLeft
                                     , bottomRight
                                     , combineSpans
                                     , spanLookup
                                     , locLookup) where

import G2.Language.Naming
import G2.Language.Syntax
import G2.Language.ExprEnv (ExprEnv)

import qualified Data.Map as M
import Data.Maybe

class Located l where
    loc :: l -> Maybe Loc

class Spanning l where
    spanning :: l -> Maybe Span

instance Located Span where
    loc = Just . start

instance Located Name where
    loc (Name _ _ _ s) = maybe Nothing loc s

instance Located Id where
    loc (Id n _) = loc n

instance Spanning Name where
    spanning (Name _ _ _ s) = s

instance Spanning Id where
    spanning (Id n _) = spanning n

-- Allows equality checking and sorting by Location
newtype Locatable a = Locatable a deriving (Show)

instance Located a => Located (Locatable a) where
    loc (Locatable x) = loc x

instance Spanning a => Spanning (Locatable a) where
    spanning (Locatable x) = spanning x

instance Located a => Eq (Locatable a) where
    x == y = loc x == loc y

instance Located a => Ord (Locatable a) where
    x `compare` y = loc x `compare` loc y

-- Allows equality checking and sorting by Span
newtype Spannable a = Spannable a deriving (Show)

instance Located a => Located (Spannable a) where
    loc (Spannable x) = loc x

instance Spanning a => Spanning (Spannable a) where
    spanning (Spannable x) = spanning x

instance Spanning a => Eq (Spannable a) where
    x == y = spanning x == spanning y

instance Spanning a => Ord (Spannable a) where
    x `compare` y = spanning x `compare` spanning y

-- | Returns the span that begins the closest to the top,
-- or, if both columns are the same, that is leftmost
topLeft :: Span -> Span -> Span
topLeft (s1@Span {start = st1}) (s2@Span {start = st2})
    | col st1 < col st2 = s1
    | col st1 > col st2 = s2
    | line st1 < line st2 = s1
    | otherwise = s2

-- | Returns the span that ends the closest to the bottom,
-- or, if both columns are the same, that is rightmost
bottomRight :: Span -> Span -> Span
bottomRight (s1@Span {end = en1}) (s2@Span {end = en2})
    | col en1 < col en2 = s2
    | col en1 > col en2 = s1
    | line en1 < line en2 = s2
    | otherwise = s1

-- | combineSpans
-- Combines two Spans into one, that covers all the characters from both spans.
-- Assumes the files are the same.
combineSpans :: Span -> Span -> Span
combineSpans s1 s2 =
    let
        tl = topLeft s1 s2
        br = bottomRight s1 s2
    in
    s1 {start = start tl, end = end br}

-- | Constructs a map of Spans to Names, based on all Names in the ExprEnv
spanLookup :: ExprEnv -> M.Map Span Name
spanLookup =
    M.fromList . mapMaybe (\n -> maybe Nothing (\s -> Just (s, n)) (spanning n)) . names

-- | Constructs a map of Locs to Names, based on all Names in the ExprEnv
locLookup :: ExprEnv -> M.Map Loc Name
locLookup = M.mapKeys start . spanLookup
