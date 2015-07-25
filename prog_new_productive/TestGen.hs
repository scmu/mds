module Main where

import System.Environment
import Control.Monad
import Control.Monad.Random

genElem :: MonadRandom m =>
   (Double, Double) -> Double -> (Int, Int) -> m (Double, Int)
genElem (vMin, vMax) vShift (wMin, wMax) =
 do v <- getRandomR (vMin, vMax)
    w <- getRandomR (wMin, wMax)
    let v' = v + vShift
    if v' > vMax then return (v, w)
                 else return (v', w)

genElems :: MonadRandom m =>
  (Double, Double) -> Double -> (Int, Int) -> Integer -> m [(Double, Int)]
genElems _ _ _ 0 = return []
genElems (vMin, vMax) vShift (wMin, wMax) n =
  do e  <- genElem  (vMin, vMax) vShift (wMin, wMax)
     es <- genElems (vMin, vMax) vShift (wMin, wMax) (n-1)
     return (e : es)

{-
Arguments:
  vMin : minimum weight
  vMax : maximum weight
  vShift : 'shifting' the weight, such that the distribution is not
           uniform. Set it to 0 for uniform distribution.
           e.g. vMin = -200, vMax = 200, vShift = 100
           generates weights between -100 and 200, with 100 "folded back".
  wMin : minimum width
  wMax : maximum width
  n    : number of elements in a list
  m    : number of lists
-}

main :: IO ()
main = do (vMin' : vMax' : vShift' : wMin' : wMax' : n' : m' : _) <- getArgs
          let vMin = read vMin'
          let vMax = read vMax'
          let vShift = read vShift'
          let wMin = read wMin'
          let wMax = read wMax'
          let n    = read n'
          let m    = read m'
          replicateM_ m
            (do es <- evalRandIO (genElems (vMin, vMax) vShift (wMin, wMax) n)
                print es)
