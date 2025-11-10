module Bif.Test where

expected :: (Eq a,Show a) => a -> String -> a -> IO ()
expected exout comment out = do
  putStr ("Expected output: " ++ show exout ++ if null comment then "" else " (" ++ comment ++ ")")
  if exout == out then putStrLn " [SUCCESS]" else putStrLn (" [FAILED: " ++ show out ++ "]")
