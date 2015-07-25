module Main where

import System.Environment
import System.IO
import Control.Monad

import ProbMDS
import MDSSeq

main :: IO ()
main = do args <- getArgs
          let lb = read (head args) :: Width

          whileM_ (liftM not isEOF)
           (do xs <- readLn :: IO [Elem]
               print (ms lb xs))

whileM_ :: (Monad m) => m Bool -> m a -> m ()
whileM_ p f = do x <- p
                 if x then do f
                              whileM_ p f
                      else return ()
