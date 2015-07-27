module Main where

import Data.List(genericReplicate)
import System.Environment
import Control.Monad
import Control.Monad.Random

type Spec = (Int, [Conf])
data Conf = R Integer (Double, Double) (Int, Int)  -- Range
          | C Integer (Double, Int)                -- Constant
   deriving (Show, Read)

-- veryLarge :: Double
-- veryLarge = 4503599627370490

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

genConf :: MonadRandom m => Conf -> m [(Double, Int)]
genConf (R n (vMin, vMax) (wMin, wMax)) = genElems (vMin, vMax) (wMin, wMax) n
genConf (C n c) = return (genericReplicate n c)

genSpec :: MonadRandom m => [Conf] -> m [(Double, Int)]
genSpec = liftM concat . mapM genConf

main :: IO ()
main = do inp <- getContents
          let (m, confs) = read inp
          replicateM_ m
            (do es <- evalRandIO (genSpec confs)
                print es)
