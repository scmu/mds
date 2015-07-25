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
