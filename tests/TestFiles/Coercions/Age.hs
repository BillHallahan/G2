module Age ( Age (..)
           , Years (..)
           , born
           , diffAge
           , yearPasses
           , age
           , Year (..)
           , YearTracker (..)
           , oneAD
           , yearBefore
           , yearAfter
           , yearBefore2) where

newtype Age = Age Int deriving Eq
newtype Years = Years Int deriving Eq

born :: Age
born = Age 0

yearPasses :: Age -> Age
yearPasses (Age a) = Age (a + 1)

diffAge :: Age -> Age -> Years
diffAge (Age a1) (Age a2) = Years (a1 - a2)

age :: Age -> Int
age (Age a) = a

newtype Year = Year Int deriving Eq
data YearTracker = AD Year | BC Year deriving Eq

oneAD :: YearTracker
oneAD = AD (Year 1)

yearBefore :: YearTracker -> YearTracker
yearBefore (AD (Year 1)) = BC (Year 1)
yearBefore (BC (Year 0 )) = error "No year 0"
yearBefore (AD (Year 0 )) = error "No year 0"
yearBefore (AD (Year x)) = AD (Year (x - 1))
yearBefore (BC (Year x)) = BC (Year (x - 1))

yearAfter :: YearTracker -> YearTracker
yearAfter (BC (Year 1)) = AD (Year 1)
yearAfter (BC (Year 0 )) = error "No year 0"
yearAfter (AD (Year 0 )) = error "No year 0"
yearAfter (AD (Year x)) = AD (Year (x + 1))
yearAfter (BC (Year x)) = BC (Year (x + 1))

yearBefore2 :: Year -> YearTracker
yearBefore2 ( (Year 1)) = BC (Year 1)
yearBefore2 ( (Year x)) = AD (Year (x - 1))
