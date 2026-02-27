module ListComp where

p1 :: [() -> Int] -> Bool
p1 u = (app <$$> u <**> [\_ -> ()] <**> [()]) == (u <**> [()])

(<**>) :: [a -> b] -> [a] -> [b]
fs <**> xs = [f x | f <- fs, x <- xs]

(<$$>) :: (a -> b) -> [a] -> [b]
f <$$> xs = [f x | x <- xs]

app :: (() -> c) -> (() -> ()) -> () -> c
app f g x = f x

p2 :: [() -> Int] -> Bool
p2 u = (app2 <$$> u <**> [()] <**> [()]) == (u <**> [()])

app2 :: (() -> c) -> () -> () -> c
app2 f g x = f x

p3 :: Eq b => [() -> b] -> Bool
p3 u = (app3 <$$> u <**> [\_ -> ()] <**> [()]) == (u <**> [()])

app3 :: (() -> c) -> (() -> ()) -> () -> c
app3 f g x = f x