{-# LANGUAGE FlexibleInstances #-}

module ProbMMS where

type Width = Int       -- or could be Num+, in general
type Day = Int
type BSReading = Double
type Weight = Double
type Density = Double

class Measurable e  where
  width :: e -> Width 
  density :: e -> Density  -- avoid using "d" 
  -- the function density is supposed to satisfy the essential properties.

lowerBound :: Width
lowerBound = 60*24*7 +1

--------------------------------------------------------------
-- Specification for the MMS Problem

data Elem = Reading {bloodSugar :: BSReading, sinceLast :: Day }
   deriving (Show, Eq)

rangeMax, rangeMin :: Double
rangeMax = 7
rangeMin = 4

outwith :: Elem -> BSReading
outwith r | b > rangeMax = b - rangeMax
          | b < rangeMin = rangeMin - b
          | otherwise = 0
  where b = bloodSugar r

weightReadings :: [Elem] -> Weight
weightReadings = sum . map outwith

instance Measurable [Elem] where
  width = sum . map sinceLast
  density x = weightReadings x / fromIntegral (length x)

 -- Memo: the information stored in data structure
 -- sufficient to compute width and density in constant time.
 
data Memo = Mem { reading :: !Double,
                  span :: !Day,
                  len :: !Int }  deriving (Show, Eq)

emptyMemo :: Memo 
emptyMemo = Mem 0 0 0

listMemo :: [Elem] -> Memo
listMemo [] = emptyMemo
listMemo x = Mem (sum (map outwith x)) (sum (map sinceLast x)) (length x)

singleMemo :: Elem -> Memo
singleMemo (rs@(Reading r s)) = Mem (outwith rs) s 1

consMemo :: Elem -> Memo -> Memo
consMemo (rd@(Reading _ s1)) (Mem r s2 l) = Mem (outwith rd + r) (s1+s2) (1+l)

desnocMemo :: Memo -> Elem -> Memo
desnocMemo (Mem r s1 l) (rd@(Reading _ s2)) = 
   Mem (r - outwith rd) (s1-s2) (l-1)

catMemo :: Memo -> Memo -> Memo
catMemo (Mem r1 s1 l1) (Mem r2 s2 l2) = 
   Mem (r1+r2) (s1+s2) (l1+l2)

decatMemoL :: Memo -> Memo -> Memo
decatMemoL (Mem r1 s1 l1) (Mem r2 s2 l2) = 
   Mem (r2-r1) (s2-s1) (l2-l1)

decatMemoR :: Memo -> Memo -> Memo
decatMemoR (Mem r1 s1 l1) (Mem r2 s2 l2) = 
   Mem (r1-r2) (s1-s2) (l1-l2)

widthMemo :: Memo -> Width
widthMemo (Mem _ s _) = s

densityMemo :: Memo -> Density
densityMemo (Mem w _ l) = w / fromIntegral l
