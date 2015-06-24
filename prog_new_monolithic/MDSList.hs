{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances #-}

module MDSList where

import Data.List
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

instance Measurable (Window Elem) where
  width = width . wflatten 
  density = density . wflatten

----------------------------------------------------------------------------
-- Window and Window Operations

type Header e = [e]

type Parts a = [a]
type Seg e = [e]

type Window e = (Header e, Parts (Seg e))

desnoc :: [a] -> Maybe ([a],a)
desnoc [] = Nothing
desnoc x = Just (init x, last x)

hsplit :: Header Elem -> (Header Elem, [Elem])
hsplit x = split (x, [])

split :: (Header Elem, [Elem]) -> (Header Elem, [Elem])
split (x,y) = case desnoc x of
   Nothing -> ([], y)
   Just (x',a) -> if width x' < lowerBound then (x,y)
                  else split (x', a:y) 

addl :: Elem -> Parts (Seg Elem) -> Parts (Seg Elem)
addl a xs = prepend [a] xs

prepend :: Seg Elem -> Parts (Seg Elem) -> Parts (Seg Elem)
prepend x [] = [x]
prepend x (y:xs) = 
    if density x <= density y 
    then prepend (x ++ y) xs
    else x : (y : xs)

drsp :: [Elem] -> Parts (Seg Elem)
drsp = foldr addl []

wbuild :: [Elem] -> Window Elem
wbuild = (id *** drsp) . hsplit 

wcons :: Elem -> Window Elem -> Window Elem
wcons a (z, xs) = (id *** foldr addl xs) . hsplit $ (a : z)

wflatten :: Window Elem -> [Elem]
wflatten (z, xs) = z ++ pflatten xs
  where pflatten = concat

maxchop :: Header Elem -> Parts (Seg Elem) -> Parts (Seg Elem)
maxchop z xs' = case desnoc xs' of
    Nothing -> []
    Just (xs, x) -> 
       if density x <= density (z, xs)
       then maxchop z xs
       else xs'

wmaxchop :: Window Elem -> Window Elem
wmaxchop (z, xs) = (z, maxchop z xs)

----------------------------------------------------------------------------
-- The Main Algorithm

ms :: [Elem] -> [Elem]
ms = fst . mwp

mwp :: [Elem] -> ([Elem],  Window Elem)
mwp [] = ([], ([], []))
mwp (a:x) = (wflatten u `cmp` m, u)
  where (m, w) = mwp x
        u = wmaxchop (wcons a w)
        cmp = bmaxby cmpElems

bmaxby :: (a -> a -> Ordering) -> a -> a -> a
bmaxby cmp x y = case cmp x y of
       LT -> y
       EQ -> x -- biased toward the left 
       GT -> x