%module Peano (Safe) [r0 :-> Data constructor ‘Zero’,
                      r1 :-> Data constructor ‘Succ’, r2 :-> Type constructor ‘Peano’,
                      r3 :-> Identifier ‘b’, r4 :-> Identifier ‘add’,
                      r5 :-> Identifier ‘a’, rjM :-> Identifier ‘hue’,
                      rpL :-> Identifier ‘Zero’, rpO :-> Identifier ‘Succ’]
hue :: Integer
[GblId, Str=DmdType]
hue =
  head @ Integer (enumFrom @ Integer $fEnumInteger (__integer 1))
add [Occ=LoopBreaker] :: Peano -> Peano -> Peano
[GblId, Arity=2, Caf=NoCafRefs, Str=DmdType]
add =
  \ (ds :: Peano) (b1 :: Peano) ->
    case ds of _ [Occ=Dead] {
      Zero -> b1;
      Succ a1 -> Succ (add a1 b1)
    };
b [Occ=LoopBreaker] :: Int -> Int
[GblId, Arity=1, Str=DmdType]
b =
  \ (ds :: Int) ->
    case ds of _ [Occ=Dead] { I# ds1 ->
    case ds1 of _ [Occ=Dead] {
      __DEFAULT ->
        + @ Int $fNumInt (+ @ Int $fNumInt (b (I# 1)) (I# 2)) (I# 1);
      0 -> I# 1
    }
    };
a :: Int -> Int
[GblId, Arity=1, Str=DmdType]
a =
  \ (ds :: Int) ->
    case ds of _ [Occ=Dead] { I# ds1 ->
    case ds1 of _ [Occ=Dead] {
      __DEFAULT -> + @ Int $fNumInt (b (I# 1)) (I# 2);
      0 -> I# 0
    }
    }
Compiles!
