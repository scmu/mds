module Main where

import System.Environment

import ProbMDS
import MDSSeq

main :: IO ()
main = do args <- getArgs
          let lb = read (head args) :: Width
          xs <- readLn :: IO [Elem]
          print (ms lb xs)
