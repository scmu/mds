module TestGen where

import System.Environment
import Control.Monad.Random

genElem :: MonadRandom m =>
   (Double, Double) -> (Int, Int) -> m (Double, Int)
genElem (vMin, vMax) (wMin, wMax) =
 do v <- getRandomR (vMin, vMax)
    w <- getRandomR (wMin, wMax)
    return (v, w)

genElems :: MonadRandom m =>
  (Double, Double) -> (Int, Int) -> Integer -> m [(Double, Int)]
genElems _ _ 0 = return []
genElems (vMin, vMax) (wMin, wMax) n =
  do e  <- genElem  (vMin, vMax) (wMin, wMax)
     es <- genElems (vMin, vMax) (wMin, wMax) (n-1)
     return (e : es)


main :: IO ()
main = do (vMin' : vMax' : wMin' : wMax' : n' : _) <- getArgs
          let vMin = read vMin'
          let vMax = read vMax'
          let wMin = read wMin'
          let wMax = read wMax'
          let n    = read n'
          es <- evalRandIO (genElems (vMin, vMax) (wMin, wMax) n)
          print es
