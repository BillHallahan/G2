module IrrefutError where

f :: Int -> Int
f x = y
  where
    Just y = if x > 0 then Nothing else Just x
