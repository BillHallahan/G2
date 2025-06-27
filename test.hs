module LiteralPCTest where

testArithmetic :: Int -> Bool
testArithmetic n = 
  	let result = n - (div n 2 * 2) -- basically n mod 2
  	in result == 0  

testConstants :: Int -> String  
testConstants n
  	| n == 14 = "a"  
  	| n == 18 = "b"   
  	| n == 21 = "c" 
  	| n == 26 = "d" 
  	| otherwise = "e"  

main :: Int -> Bool
main n = 
  	testArithmetic n && 
  	(testConstants n /= "e")