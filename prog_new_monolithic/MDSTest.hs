module MDSTest where

import Prelude hiding (abs)

import Test.QuickCheck

import ProbMDS
import MDSList

prop_mds_correct :: Weight -> Width -> Property
prop_mds_correct uweight ubreadth =
   forAll (longer uweight ubreadth) $
     \x -> ms x `eqd` mds_spec x

 --- generate test samples

longer :: Weight -> Width -> Gen [Elem]
longer uweight ubreadth = sized (longer' lowerBound)
 where longer' lb 0 = do Item a w <- genElem
                         if w > lb then return [Item a w]
                          else do x <- longer' (lb - w) 0
                                  return (Item a w : x)
       longer' lb n = do a <- genElem
                         x <- longer' lb (n - 1)
                         return (a : x)
       genElem :: Gen Elem
       genElem = do a <- choose (-uweight, uweight)
                    w <- if ubreadth == 1 then return 1
                            else choose (1, ubreadth) -- element breadth between 1 and ubreadth
                    return (Item a w)

x `eqd` y = density x == density y
