module MDS where

open import Data.Empty
open import Function using (_∘_; id)
open import Data.Product
open import Data.Nat
open import Data.List

open import Relation.Nullary
open import Relation.Binary

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Elem
open import List+
open import Prefix
open import Utilities using (SnocWF; []; ∷ʳ-wf; snocWF; _╳_)

max-with : ∀ {A} → (A → A → A) → List⁺ A → A
max-with _↑_ [ x ]⁺ = x
max-with _↑_ (x ∷ xs) = x ↑ max-with _↑_ xs

max≼ : List⁺ (List Elem) → List Elem
max≼ = max-with _↑≼_
-- max≼ [ x ]⁺ = x
-- max≼ (x ∷ xs) = x ↑≼ max≼ xs

maxd : List⁺ (List Elem) → List Elem
maxd = max-with _↑d_
-- maxd [ x ]⁺ = x
-- maxd (x ∷ xs) = x ↑d maxd xs

mdp : List Elem → List Elem
mdp = max≼ ∘ prefixes

mds : List Elem → List Elem
mds [] = []
mds (a ∷ x) = mdp (a ∷ x) ↑≼ mds x

-- 

wp : List Elem → List Elem
wp [] = []
wp (a ∷ x) = mdp (a ∷ wp x) 

ms : List Elem → List Elem
ms [] = []
ms (a ∷ x) = wp (a ∷ x) ↑≼ ms x

wps : List Elem → List⁺ (List Elem)
wps = scanr⁺ (λ a x → mdp (a ∷ x)) []
{-
wps [] = [ [] ]⁺
wps (a ∷ x) = mdp (a ∷ head⁺ xs) ∷ xs
  where xs = wps x -}

--

maxchop : List Elem → (xs : List (List Elem)) → SnocWF xs → List (List Elem)
maxchop z .[] [] = []
maxchop z .(xs ++ [ x ]) (∷ʳ-wf xs wf x) 
  with x ≤d? (z ++ concat xs)
... | no _ {- z ++ concat xs <d x -} = xs ++ [ x ]
... | yes _ = maxchop z xs wf

prepend : List Elem → List (List Elem) → List (List Elem)
prepend x [] = [ x ]
prepend x (y ∷ xs) with x ≤d? y
... | yes _ = prepend (x ++ y) xs
... | no _ = x ∷ (y ∷ xs)

addl : Elem → List (List Elem) → List (List Elem)
addl a xs = prepend [ a ] xs

drsp : List Elem → List (List Elem)
drsp = foldr addl []

-- window

Window : Set
Window = List Elem × List (List Elem)

wflatten : Window → List Elem
wflatten (z , xs) = z ++ concat xs

postulate hsplit : List Elem → (List Elem × List Elem)

wbuild : List Elem → Window
wbuild x with hsplit x
... | (z , x') = (z , drsp x')

-- wbuild = (id ╳ drsp) ∘ hsplit

wcons : Elem → Window → Window
wcons a (z , xs) with hsplit (a ∷ z)
... | (z' , x') = (z' , foldr addl xs x')

wmaxchop : Window → Window
wmaxchop (z , xs) = (z , maxchop z xs (snocWF xs))

{-
data Window : List Elem → Set where
  win : ∀ z → -}
