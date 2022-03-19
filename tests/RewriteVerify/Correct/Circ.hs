module Circ where

data Stream a = Cons a (Stream a) deriving (Show, Eq)

streamHead :: Stream a -> a
streamHead (Cons a _) = a

streamTail :: Stream a -> Stream a
streamTail (Cons _ s) = s

streamOdd :: Stream a -> Stream a
streamOdd (Cons a s) = Cons a (streamEven s)

streamEven :: Stream a -> Stream a
streamEven (Cons a s) = streamOdd s

-- TODO two arguments or tuple?
streamZip :: (Stream a, Stream a) -> Stream a
streamZip (Cons a s, s') = Cons a (streamZip (s', s))

data Bit = Z | O deriving (Show, Eq)

ozo :: Stream Bit
ozo = Cons O $ Cons Z $ Cons O $ ozo

feigenbaum :: Stream Bit
feigenbaum = Cons O $ Cons Z $ Cons O $ Cons O $ Cons O $ Cons Z $
             Cons O $ Cons Z $ Cons O $ Cons Z $ Cons O $ Cons O feigenbaum

zip31 :: (Stream a, Stream a) -> Stream a
zip31 (Cons a0 (Cons a1 (Cons a2 s)), Cons b s') =
  Cons a0 $ Cons a1 $ Cons a2 $ Cons b $ zip31 (s, s')

-- TODO need to use a different type for some theorems to work
notBit :: Bit -> Bit
notBit Z = O
notBit O = Z

notStream :: Stream Bit -> Stream Bit
notStream (Cons a s) = Cons (notBit a) (notStream s)

f :: Stream Bit -> Stream Bit
f (Cons a s) = Cons a $ Cons (notBit a) $ f s

morse :: Stream Bit
morse = Cons Z $ streamZip (notStream morse, streamTail morse)

ones :: Stream Bit
ones = Cons O ones

extractOnes :: Stream Bit -> Stream Bit
extractOnes (Cons b s) =
  if b == O
  then Cons O $ extractOnes s
  else extractOnes s

g1 :: Stream Bit
g1 = Cons Z $ notStream g3

g2 :: Stream Bit
g2 = Cons Z $ notStream g1

g3 :: Stream Bit
g3 = Cons Z $ notStream g2

data Alph = A | B deriving (Show, Eq)

data AState = S0 | S1 | S2 | S99 deriving (Show, Eq)

-- TODO how do I phrase example 5 as a rewrite rule?
delta :: (AState, Alph) -> AState
delta (S0, A) = S1
delta (S0, B) = S2
delta (S1, A) = S2
delta (S1, B) = S2
delta (S2, A) = S2
delta (S2, B) = S2
delta (S99, A) = S99
delta (S99, B) = S99

altMorse :: Stream Bit
altMorse = f $ Cons Z $ streamTail altMorse

-- TODO the verifier gets stuck on zipOddEven at printing a0
-- it gets stuck for some of the others as well
-- adding Show to the types didn't help
-- (2/1) ex3a gets stuck even with state printing disabled
-- same goes for ex3b, ex4, ex6a
-- I get UNSAT for ex1, ex2, ex6b with state printing disabled
{-
(2/11)
I get UNSAT for ex1, ex2, ex6b
ex3a fails to terminate but doesn't get stuck
Same for ex3b, ex4, ex6a
-}
{-# RULES
"ex1" forall s . streamZip (streamOdd s, streamEven s) = s
"ex2" zip31 (ozo, ozo) = feigenbaum
"ex3a" f morse = morse
"ex3b" f (notStream morse) = notStream morse
"ex4" extractOnes g1 = ones
"ex6a" morse = altMorse
"ex6b" forall s . f s = streamZip (s, notStream s)
  #-}
