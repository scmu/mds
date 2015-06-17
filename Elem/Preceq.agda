module Elem.Preceq where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary

open import Utilities using (≤-refl; ≤-trans)

open import Elem.Core

infix 4 _≼_ _≺_

data _≼_ : List Elem → List Elem → Set where
  ≼-initial : ∀ {x y} 
              → ¬ (we x) → ¬ (we y)
              → width x ≤ width y
              → x ≼ y
  ≼-triv : ∀ {x y} 
              → ¬ (we x) → we y
              → x ≼ y
  ≼-density : ∀ {x y} 
              → we x → we y
              → x ≤d y
              → x ≼ y

_≺_ : List Elem → List Elem → Set
x ≺ y = x ≼ y × ¬ (y ≼ x)

≼-refl : ∀ {x} → x ≼ x
≼-refl {x} with we? x
... | no □ = ≼-initial □ □ ≤-refl
... | yes ⊠ = ≼-density ⊠ ⊠ ≤d-refl

≼-trans : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z
≼-trans (≼-initial □x □y x≤wy) (≼-initial _ □z y≤wz) = ≼-initial □x □z (≤-trans x≤wy y≤wz)
≼-trans (≼-initial □x □y x≤wy) (≼-density ⊠y _ _) = ⊥-elim (□y ⊠y)
≼-trans (≼-initial □x □y x≤wy) (≼-triv _ ⊠z) = ≼-triv □x ⊠z
≼-trans (≼-triv _ ⊠y) (≼-initial □y _ _) = ⊥-elim (□y ⊠y)
≼-trans (≼-triv □x ⊠y) (≼-density _ ⊠z y≤dz) = ≼-triv □x ⊠z
≼-trans (≼-triv y' ⊠y) (≼-triv □y y2) = ⊥-elim (□y ⊠y)
≼-trans (≼-density ⊠x ⊠y x≤dy) (≼-initial □y _ _) = ⊥-elim (□y ⊠y)
≼-trans (≼-density ⊠x ⊠y x≤dy) (≼-triv □y ⊠z) = ⊥-elim (□y ⊠y)
≼-trans (≼-density ⊠x ⊠y x≤dy) (≼-density _ ⊠z y≤dz) = ≼-density ⊠x ⊠z (≤d-trans x≤dy y≤dz)

<d→≺ : ∀ {x y} → we x → we y → ¬ (y ≤d x) → x ≺ y
<d→≺ {x} {y} ⊠x ⊠y x<dy = (≼-density ⊠x ⊠y (<d→≤d x<dy)) , ¬y≼x
  where ¬y≼x : y ≼ x → ⊥
        ¬y≼x (≼-initial □y _ _) = □y ⊠y
        ¬y≼x (≼-triv □y _) = □y ⊠y
        ¬y≼x (≼-density _ _ y≤dx) = x<dy y≤dx

≼→≤d : ∀ {x y} → we x → x ≼ y → x ≤d y
≼→≤d {x} {y} ⊠x (≼-initial □ _ _) = ⊥-elim (□ ⊠x)
≼→≤d {x} {y} ⊠x (≼-triv □ _) = ⊥-elim (□ ⊠x)
≼→≤d {x} {y} ⊠x (≼-density _ _ ≤d) = ≤d

postulate
  ≺→<d : ∀ {x y} → we x → x ≺ y → x <d y

≼-≺-trans : ∀ {x y z} → x ≼ y → y ≺ z → x ≺ z
≼-≺-trans x≼y (y≼z , ¬z≼y) = (≼-trans x≼y y≼z , λ z≼x → ¬z≼y (≼-trans z≼x x≼y))


_≼?_ : Decidable _≼_
x ≼? y with we? x | we? y
x ≼? y | yes xOk | yes yOk with x ≤d? y
x ≼? y | yes xOk | yes yOk | yes x≤dy = yes (≼-density xOk yOk x≤dy)
x ≼? y | yes xOk | yes yOk | no x>dy = no neg
  where neg : ¬ (x ≼ y)
        neg (≼-initial ¬xOk _ _) = ¬xOk xOk
        neg (≼-density _ _ x≤dy) = x>dy x≤dy
        neg (≼-triv ¬xOk _) = ¬xOk xOk
x ≼? y | yes xOk | no ¬yOk = no neg
  where neg : ¬ (x ≼ y)
        neg (≼-initial ¬xOk _ _) = ¬xOk xOk
        neg (≼-density _ yOk _) = ¬yOk yOk
        neg (≼-triv ¬xOk _) = ¬xOk xOk
x ≼? y | no ¬xOk | yes yOk = yes (≼-triv ¬xOk yOk)
x ≼? y | no ¬xOk | no ¬yOk with width x ≤? width y
x ≼? y | no ¬xOk | no ¬yOk | yes x≤wy = yes (≼-initial ¬xOk ¬yOk x≤wy)
x ≼? y | no ¬xOk | no ¬yOk | no x>wy = no neg
  where neg : ¬ (x ≼ y)
        neg (≼-initial _ _ x≤wy) = x>wy x≤wy
        neg (≼-density xOk _ _) = ¬xOk xOk
        neg (≼-triv _ yOk) = ¬yOk yOk

{- 
 
  -- This definition appears awkward in proofs.

_↑≼_ : List Elem → List Elem → List Elem
x ↑≼ y with x ≼? y
... | yes _ = y
... | no _ = x
-}

_↑≼_ : List Elem → List Elem → List Elem
x ↑≼ y with we? x | we? y
x ↑≼ y | yes xOk | yes yOk = x ↑d y
x ↑≼ y | yes xOk | no ¬yOk = x
x ↑≼ y | no ¬xOk | yes yOk = y
x ↑≼ y | no ¬xOk | no ¬yOk with width y ≤? width x
x ↑≼ y | no ¬xOk | no ¬yOk | yes y≤wx = x
x ↑≼ y | no ¬xOk | no ¬yOk | no y>wx = y  

postulate
  Choose-↑≼ : Choose _↑≼_