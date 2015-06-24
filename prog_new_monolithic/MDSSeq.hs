{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances,
             ViewPatterns #-}

module MDSSeq where

import Data.List
import Data.Sequence (Seq(..), singleton, empty,
                      ViewL(..), viewl, (<|),
                      ViewR(..), viewr, (|>) )
import Control.Arrow ((***))

import ProbMDS

----------------------------------------------------------------------------
-- Basic definitions

wide :: Measurable e => e -> Bool
wide x = width x >= lowerBound

cmpElems :: Measurable e => e -> e -> Ordering
cmpElems x y = case (wide x, wide y) of
        (False, False) -> compare (width x) (width y)
        (False, True ) -> LT
        (True,  False) -> GT
        (True,  True ) -> compare (density x) (density y)

----------------------------------------------------------------------------
-- General Specification

segments = concat . map inits . tails

mds_spec :: Measurable [e] => [e] -> [e]
mds_spec = maximumBy cmpElems . segments

instance Measurable [[Elem]] where
  width = width . concat
  density = density . concat

instance Measurable Header where
  width   (Head _ m) = widthMemo m
  density (Head _ m) = densityMemo m

instance Measurable Window where
  width   (Win (Head _ m) (Parts _ n)) = widthMemo (catMemo m n)
  density (Win (Head _ m) (Parts _ n)) = densityMemo (catMemo m n)

instance Measurable Seg where
  width   (Seg _ m) = widthMemo m
  density (Seg _ m) = densityMemo m

----------------------------------------------------------------------------
-- Window and Window Operations

data Header = Head ([Elem], [Elem]) !Memo  deriving (Show, Eq)

data Parts = Parts (Seq Seg) !Memo         deriving (Show, Eq)
data Seg = Seg Seg' !Memo                  deriving (Show, Eq)
data Seg' = Single Elem | Join Seg' Seg'   deriving (Show, Eq)

data Window = Win Header Parts             deriving (Show, Eq)

hnil :: Header
hnil = Head ([],[]) emptyMemo

hcons :: Elem -> Header -> Header
hcons a (Head (x,y) m) = Head (a:x, y) (consMemo a m)

hdesnoc :: Header -> Maybe (Header, Elem)
hdesnoc (Head ([],[]) _)   = Nothing
hdesnoc (Head (x,[]) m)    = hdesnoc (Head ([], reverse x) m)
hdesnoc (Head (x, a:y) m) = Just (Head (x,y) (desnocMemo m a), a) 

hflatten :: Header -> [Elem]
hflatten (Head (x,y) _) = x ++ reverse y

segSingle :: Elem -> Seg
segSingle a = Seg (Single a) (singleMemo a)

segJoin :: Seg -> Seg -> Seg
segJoin (Seg x m) (Seg y n) = Seg (x `Join` y) (catMemo m n)

sflatten :: Seg -> [Elem]
sflatten (Seg x _) = sflatten' x
 
sflatten' :: Seg'-> [Elem]
sflatten' (Single a) = [a]
sflatten' (Join x y) = sflatten' x ++ sflatten' y

pflatten :: Parts -> [Elem]
pflatten (Parts xs _) = pflatten' xs
 where pflatten' (viewl -> EmptyL) = []
       pflatten' (viewl -> x :< xs) = sflatten x ++ pflatten' xs

pnil :: Parts
pnil = Parts empty emptyMemo

pcons :: Seg -> Parts -> Parts
pcons (Seg x m) (Parts xs n) = 
  Parts ((Seg x m) <| xs) (catMemo m n)

psnoc :: Parts -> Seg -> Parts
psnoc (Parts xs m) (Seg x n) = 
  Parts (xs |> (Seg x n)) (catMemo m n)

pviewl :: Parts -> Maybe (Seg, Parts)
pviewl (Parts xs m) 
    | EmptyL <- viewl xs = Nothing
    | (Seg y n) :< xs' <- viewl xs =  Just (Seg y n, Parts xs' (decatMemoL n m))

pviewr :: Parts -> Maybe (Parts, Seg)
pviewr (Parts xs m) 
    | EmptyR <- viewr xs = Nothing
    | xs' :> (Seg y n) <- viewr xs =  Just (Parts xs' (decatMemoR m n), Seg y n)

--- Window Operations

hsplit :: Header -> (Header, [Elem])
hsplit x = split (x, [])

split :: (Header, [Elem]) -> (Header, [Elem])
split (x,y) = case hdesnoc x of
   Nothing -> (hnil, y)
   Just (x',a) -> if width x' < lowerBound then (x,y)
                  else split (x', a:y) 

addl :: Elem -> Parts -> Parts
addl a xs = prepend (segSingle a) xs

prepend :: Seg -> Parts -> Parts
prepend (Seg x m) (pviewl -> Nothing) = 
    Parts (singleton (Seg x m)) m
prepend x (pviewl -> Just (y, xs)) = 
    if density x <= density y 
    then prepend (x `segJoin` y) xs
    else x `pcons` (y `pcons` xs)

drsp :: [Elem] -> Parts
drsp = foldr addl pnil

wbuild :: [Elem] -> Window 
wbuild x = uncurry Win . (id *** drsp) . hsplit $ 
             Head (x,[]) (listMemo x)

wcons :: Elem -> Window -> Window 
wcons a (Win z xs) = 
   uncurry Win . (id *** foldr addl xs) . hsplit $ 
                    (a `hcons` z)

wflatten :: Window -> [Elem]
wflatten (Win z xs) = hflatten z ++ pflatten xs

maxchop :: Header -> Parts -> Parts
maxchop z (pviewr -> Nothing) = pnil
maxchop z (pviewr -> Just (xs, x)) = 
       if density x <= density (Win z xs)
       then maxchop z xs
       else xs `psnoc` x

wmaxchop :: Window -> Window
wmaxchop (Win z xs) = Win z (maxchop z xs)

----------------------------------------------------------------------------
-- The Main Algorithm

ms :: [Elem] -> [Elem]
ms = wflatten . fst . mwp

mwp :: [Elem] -> (Window,  Window)
mwp [] = (Win hnil pnil, Win hnil pnil)
mwp (a:x) = (u `cmp` m, u)
  where (m, w) = mwp x
        u = wmaxchop (wcons a w)
        cmp = bmaxby cmpElems

bmaxby :: (a -> a -> Ordering) -> a -> a -> a
bmaxby cmp x y = case cmp x y of
       LT -> y
       EQ -> x -- biased toward the left 
       GT -> x