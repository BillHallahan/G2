data ShapeType = Circle | Rectangle

data Shape where
  CircleShape :: Double -> Shape
  RectangleShape :: Double -> Double -> Shape

area :: Shape -> Double
area (CircleShape radius) = pi * radius * radius
area (RectangleShape width height) = width * height


