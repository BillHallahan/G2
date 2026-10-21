module ListComp2 where

data X = X

instance Eq X where
    X == X = True

prop :: (X -> [X]) -> Bool
prop k = [y | x <- [X], y <- k x] == k X

prop2 :: (X -> [X]) -> Bool
prop2 k = (let
      g x = (case x of
            []  -> []
            y : ys -> let
                  f w = (case w of
                        []  -> g ys
                        z : zs -> z:f zs) in f (k y)) in g ([X])) == (k X)
