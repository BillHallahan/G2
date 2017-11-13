module NewType1 ( Age
                , born
                , yearPasses
                , age) where

newtype Age = Age Int

born :: Age
born = Age 0

yearPasses :: Age -> Age
yearPasses (Age a) = Age (a + 1)

age :: Age -> Int
age (Age a) = a