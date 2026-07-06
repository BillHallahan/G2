{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HigherChar1 where

type Env = String -> Int
          
eval1 :: Env -> Maybe Env
eval1 env =
  Just $ \x -> case x == "i" of
                    True  -> env "i" + 1
                    False -> env x

eval2 :: Env -> Maybe Env            
eval2 env =
  if env "i" == env "n"
    then eval1 env >>= \env' -> eval2 env'
    else Just env  

eval :: Env -> Bool
eval env = case eval2 env of
      Just _ -> True
      Nothing -> error "Assertion violation"