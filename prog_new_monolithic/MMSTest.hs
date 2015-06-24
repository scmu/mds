module MMSTest where

import Prelude hiding (abs)

import Test.QuickCheck

import ProbMMS
import MDSSeq

prop_mds_correct :: BSReading -> Day -> Property
prop_mds_correct ureading ubreadth =
   forAll (longer ureading ubreadth) $
     \x -> ms x `eqd` mds_spec x

 --- generate test samples

longer :: BSReading -> Day -> Gen [Elem]
longer ureading ubreadth = sized (longer' lowerBound)
 where longer' lb 0 = do Reading r s <- genElem
                         if s > lb then return [Reading r s]
                          else do x <- longer' (lb - s) 0
                                  return (Reading r s : x)
       longer' lb n = do a <- genElem
                         x <- longer' lb (n - 1)
                         return (a : x)
       genElem :: Gen Elem
       genElem = do r <- choose (1, ureading)
                    s <- if ubreadth == 1 then return 1
                            else choose (1, ubreadth) -- element breadth between 1 and ubreadth
                    return (Reading r s)

x `eqd` y = density x == density y