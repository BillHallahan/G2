module Prim3 where

float2IntTest :: Float -> Bool
float2IntTest x = fromEnum x == 597

double2IntTest :: Double -> Bool
double2IntTest x = fromEnum x == 597

int2FloatTest :: Int -> Bool
int2FloatTest x = toEnum x == (597 :: Float)

int2DoubleTest :: Int -> Bool
int2DoubleTest x = toEnum x == (597 :: Double)