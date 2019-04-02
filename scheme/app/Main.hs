module Main where

import Lib

main :: IO ()
main =
  do prog <- getContents
     tryRun prog

  
