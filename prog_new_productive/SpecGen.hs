module Main where
import System.Environment

type Spec = (Int, [Conf])
data Conf = R Integer (Double, Double) (Int, Int)  -- Range
          | C Integer (Double, Int)                -- Constant
  deriving (Show, Read)


veryLarge :: Double
veryLarge = 4503599627370490
 -- close to the largest number representable by Double

veryLargeH :: Double
veryLargeH = 2003599627370490
 -- less than half of veryLarge

specGen' :: (Double, Double) -> (Int, Int) -> Integer -> Integer -> [Conf]
specGen' vR wR m n
  | n <= 0 = error "n <= 0"
  | n < m + 1 = [R n vR wR]
  | otherwise = [C 1 (veryLarge,1)] ++
                [R m vR wR] ++
                specGen' vR wR m (n - m - 1)

specGen :: (Double, Double) -> (Int, Int) -> Integer -> Integer -> [Conf]
specGen vR wR m n
  | n > m = [R m vR wR] ++ specGen' vR wR m (n - m)
  | otherwise = []

main :: IO ()
main = do (vMin' : vMax' : wMin' : wMax' : k' : n' : m' : _) <- getArgs
          let vMin = read vMin'
          let vMax = read vMax'
          let wMin = read wMin'
          let wMax = read wMax'
          let k    = read k' :: Int
          let n    = read n'
          let m    = read m'
          print (k, specGen (vMin, vMax) (wMin, wMax) m n)
