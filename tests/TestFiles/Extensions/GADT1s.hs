-- {-# LANGUAGE GADTs #-}

module GADTS1 where

data ShapeType = Circle | Rectangle

data Shape = CircleShape Double | RectangleShape Double Double

-- data Shape where
--   CircleShape :: Double -> Shape
--   RectangleShape :: Double -> Double -> Shape

area :: Shape -> Double
area (CircleShape radius) = pi * radius * radius
area (RectangleShape width height) = width * height


