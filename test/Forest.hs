module Forest where

data Forest = NilF | ConsF {carF :: Tree, cdrF :: Forest}
data Tree = NilT | ConsT {carT :: Forest, cdrT :: Forest}

