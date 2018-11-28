module Prim3 where

int2FloatTest :: Float -> Bool
int2FloatTest x = fromEnum x == 597

int2DoubleTest :: Double -> Bool
int2DoubleTest x = fromEnum x == 597

float2IntTest :: Int -> Bool
float2IntTest x = toEnum x == (597 :: Float)

double2IntTest :: Int -> Bool
double2IntTest x = toEnum x == (597 :: Double)