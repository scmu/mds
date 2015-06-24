{-# LANGUAGE FlexibleInstances #-}

module ProbMDS where

--------------------------------------------------------------
-- Specification for the MDS Problem


type Width = Int       -- or could be Num+, in general
type Weight = Double
type Density = Double

lowerBound :: Width
lowerBound = 16

class Measurable e  where
  width :: e -> Width 
  density :: e -> Density  -- avoid using "d" 
  -- the function density is supposed to satisfy the essential properties.

type Area = Double

data Elem = Item { weightItem :: Area, sizeItem :: Width } -- (Num, Num+)
  deriving (Show, Eq)

weightItems :: [Elem] -> Area
weightItems = sum . map weightItem

sizeItems :: [Elem] -> Width
sizeItems = sum . map sizeItem

instance Measurable [Elem] where
  width = sizeItems
  density x = weightItems x / fromIntegral (sizeItems x)

instance Show Elem where
  showsPrec _ (Item v s) = ('(':) . showsPrec 0 v . (',':) .
                             showsPrec 0 s . (')':)

 -- Memo: the information stored in data structure
 -- sufficient to compute width and density in constant time.

data Memo = Mem { weightC :: !Area, sizeC :: !Width } -- (Num, Num+)
       deriving (Show, Eq)

emptyMemo :: Memo 
emptyMemo = Mem 0 0

listMemo :: [Elem] -> Memo
listMemo x = Mem (weightItems x) (sizeItems x)

singleMemo :: Elem -> Memo
singleMemo (Item w s) = Mem w s

consMemo :: Elem -> Memo -> Memo
consMemo (Item w1 s1) (Mem w2 s2) = Mem (w1+w2) (s1+s2)

desnocMemo :: Memo -> Elem -> Memo
desnocMemo (Mem w1 s1) (Item w2 s2) = Mem (w1-w2) (s1-s2)

catMemo :: Memo -> Memo -> Memo
catMemo (Mem w1 s1) (Mem w2 s2) = Mem (w1+w2) (s1+s2)

decatMemoL :: Memo -> Memo -> Memo
decatMemoL (Mem w1 s1) (Mem w2 s2) = Mem (w2-w1) (s2-s1)

decatMemoR :: Memo -> Memo -> Memo
decatMemoR (Mem w1 s1) (Mem w2 s2) = Mem (w1-w2) (s1-s2)

widthMemo :: Memo -> Width
widthMemo (Mem _ s) = s

densityMemo :: Memo -> Density
densityMemo (Mem w s) = w / fromIntegral s