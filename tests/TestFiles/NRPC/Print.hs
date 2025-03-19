module Print where

f :: Int -> IO ()
f x = do
    case show x of
            '-':_ -> putStrLn "!"
            _ -> print x