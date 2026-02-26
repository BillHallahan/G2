module Maybe1 where

p1 :: Eq b => Maybe (() -> b) -> Bool
p1 u = (Just (.) <*> u <*> Just (\_ -> ()) <*> (Just ())) == (u <*> (Just ()))
