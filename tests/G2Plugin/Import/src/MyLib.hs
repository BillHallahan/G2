module MyLib where

data MyInt = MyInt Int | MyIntAlso Int

call :: MyInt -> Int
call (MyInt x) = x * 2
call (MyIntAlso x) = x * 4
