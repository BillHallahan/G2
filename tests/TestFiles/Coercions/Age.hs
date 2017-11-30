module NewType1 ( Age
                , born
                , diffAge
                , yearPasses
                , age) where

newtype Age = Age Int
newtype Years = Years Int

born :: Age
born = Age 0

yearPasses :: Age -> Age
yearPasses (Age a) = Age (a + 1)

diffAge :: Age -> Age -> Years
diffAge (Age a1) (Age a2) = Years (a1 - a2)

age :: Age -> Int
age (Age a) = a