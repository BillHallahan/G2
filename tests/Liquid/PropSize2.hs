{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}

module PropSize2 where

import Prelude hiding (length)

data List = Emp
          | C List

-- length :: Num a => List -> a
length Emp = 0
length (C xs) = length xs

prop_size =
    case length Emp of
        0 -> True
        _ -> die "Assert fails!"

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)