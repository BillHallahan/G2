module Maybe1 where

p1 :: Eq b => Maybe (() -> b) -> Bool
p1 u = (Just app <**> u <**> (Just ())) == (u <**> (Just ()))

(<**>) :: Maybe (a -> b) -> Maybe a -> Maybe b
Just f  <**> m = fmap f m
Nothing <**> _ = Nothing

infixl 4 <**>

app :: (() -> c) -> () -> c
app f = f