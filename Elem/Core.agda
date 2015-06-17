module Elem.Core where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary hiding (NonEmpty)

open import Utilities using (NonEmpty; _∷_)

open import Relation.Binary.PropositionalEquality
import AlgebraicReasoning.MonoPreorderReasoning as MPR

postulate Elem : Set

infix 4 _≤d_ _<d_ _>d_ _≥d_

postulate _≤d_ : List Elem → List Elem → Set

_<d_ : List Elem → List Elem → Set
x <d y = ¬ (y ≤d x)

_≥d_ : List Elem → List Elem → Set
x ≥d y = y ≤d x

_>d_ : List Elem → List Elem → Set
x >d y = y <d x

postulate ≤d-refl : ∀ {x} → x ≤d x
postulate ≤d-trans : ∀ {x y z} → x ≤d y → y ≤d z → x ≤d z
postulate ≤d-total : ∀ {x y} → (x ≤d y) ⊎ (y ≤d x) 

{- 
   Essential properties: for non-empty x and y

   x <d x ++ y  ↔  x <d y  ↔  x++y <d y
   x ≤d x ++ y  ↔  x ≤d y  ↔  x++y ≤d y 
-}

postulate
  ≤d-++→≤d : ∀ {x y} → NonEmpty x → NonEmpty y → x ≤d x ++ y → x ≤d y
  ≤d→++-≤d : ∀ {x y} → NonEmpty x → NonEmpty y → x ≤d y → x ++ y ≤d y
  ≤d→≤d-++ : ∀ {x y} → NonEmpty x → NonEmpty y → x ≤d y → x ≤d x ++ y
  ++-≤d→≤d : ∀ {x y} → NonEmpty x → NonEmpty y → x ++ y ≤d y → x ≤d y

  ≥d-++→≥d : ∀ {x y} → NonEmpty x → NonEmpty y → x ≥d x ++ y → x ≥d y
  ≥d→≥d-++ : ∀ {x y} → NonEmpty x → NonEmpty y → x ≥d y → x ≥d x ++ y

  <d→++-<d : ∀ {x y} → NonEmpty x → NonEmpty y → x <d y → x ++ y <d y
  <d→<d-++ : ∀ {x y} → NonEmpty x → NonEmpty y → x <d y → x <d x ++ y 
  ++-<d→<d : ∀ {x y} → NonEmpty x → NonEmpty y → x ++ y <d y → x <d y 

  >d→>d-++ : ∀ {x y} → NonEmpty x → NonEmpty y → x >d y → x >d x ++ y 

{- Not needed if we assume the ≥d and >d properties of the section above.
postulate
  ≤d-++ : ∀ x y → x ++ y ≤d y ++ x
-}

postulate _≤d?_ : Decidable _≤d_
postulate -- because densities are numbers
  <d→≤d : ∀ {x y} → ¬ (y ≤d x) → x ≤d y
  d-tri : ∀ {x} y {z} → x ≤d z → x ≤d y ⊎ y ≤d z
  <d-trans : ∀ {x y z} → x <d y → y <d z → x <d z
  ≤d<d-trans : ∀ {x y z} → x ≤d y → y <d z → x <d z
  <d≤d-trans : ∀ {x y z} → x <d y → y ≤d z → x <d z

module ≤d-reasoning = MPR.Mono _≤d_ ≤d-refl ≤d-trans
  renaming (begin_ to ≤d-begin_ ; _∼⟨_⟩_ to _≤d⟨_⟩_ ; _∎ to _≤d∎)

Width : Set
Width = ℕ

postulate L : Width
postulate width : List Elem → Width

we : List Elem → Set   -- we = wide enough
we x = L ≤ width x

_≤w_ : List Elem → List Elem → Set
x ≤w y = width x ≤ width y

postulate 
  L-positive : ¬ (we [])

postulate
  we-∷ : ∀ a {x} → we x → we (a ∷ x)
  ¬we-∷ : ∀ {a x} → ¬ (we (a ∷ x)) → ¬ we x
  ¬we-snoc : ∀ {x a} → ¬ (we (x ++ a ∷ [])) → ¬ we x

  -- width-[] : ∀ x → width [] ≤ width x
  width-[] : ∀ {x} → width x ≤ width [] → x ≡ []
  width-∷ : ∀ a x →  width x ≤ width (a ∷ x)
  width-snoc : ∀ x a → ¬ (width (x ++ a ∷ []) ≤ width x) -- not good enough...


{-
we-nonempty : ∀ {x} → we x → ∃ (λ a → ∃ (λ y → x ≡ a ∷ y))
we-nonempty {[]} ⊠x = ⊥-elim (L-positive ⊠x)
we-nonempty {a ∷ y} ⊠x = a , y , refl
-}

we-nonempty : ∀ {x} → we x → NonEmpty x
we-nonempty {[]} ⊠x = ⊥-elim (L-positive ⊠x)
we-nonempty {a ∷ y} ⊠x = a ∷ y

we-++ : ∀ u {x} → we x → we (u ++ x)
we-++ [] ⊠x = ⊠x
we-++ (a ∷ u) ⊠x = we-∷ a (we-++ u ⊠x)

postulate
 we-++₂ : ∀ u {x} → we x → we (x ++ u)

we? : (x : List Elem) → Dec (L ≤ width x)
we? x = L ≤? width x

_≤w?_ : ∀ x y → Dec (width x ≤ width y)
x ≤w? y = width x ≤? width y

_↑d_ : List Elem → List Elem → List Elem
x ↑d y with y ≤d? x
x ↑d y | yes y≤dx = x
x ↑d y | no y>dx = y

Assoc : ∀{A : Set} → (A → A → A) → Set
Assoc _↑_ = ∀ x y z → x ↑ (y ↑ z) ≡ (x ↑ y) ↑ z

Idem : ∀{A : Set} → (A → A → A) → Set
Idem _↑_ = ∀ x → x ↑ x ≡ x

Choose : ∀{A : Set} → (A → A → A) → Set
Choose _↑_ = ∀ x y → (x ↑ y ≡ x) ⊎ (x ↑ y ≡ y)

Choose-Left : ∀ {A : Set} 
              → (A → A → A) → (A → A → Set) → Set
Choose-Left {A} _↑_ _≼_ = 
    ∀ x y → ((x ↑ y ≡ x) × y ≼ x) ⊎ 
            ((x ↑ y ≡ y) × x ≺ y)
 where _≺_ : A → A → Set
       x ≺ y =  x ≼ y × ¬ (y ≼ x)

Choose-Left⇒Choose : ∀ {A : Set} {↑ : A → A → A} {≼ : A → A → Set}
                     → Choose-Left ↑ ≼ → Choose ↑
Choose-Left⇒Choose chl x y with chl x y
... | inj₁ (eq , _) = inj₁ eq
... | inj₂ (eq , _) = inj₂ eq

postulate 
  ↑d-assoc : ∀ x y z → x ↑d (y ↑d z) ≡ (x ↑d y) ↑d z

↑d-idem : ∀ x → x ↑d x ≡ x
↑d-idem x with x ≤d? x
... | yes _ = refl
... | no x<x = ⊥-elim (x<x ≤d-refl)

↑d-left : ∀ {x y} → y ≤d x → x ↑d y ≡ x
↑d-left {x} {y} y≤x with y ≤d? x
... | yes _ = refl
... | no x<y = ⊥-elim (x<y y≤x)

↑d-right : ∀ {x y} → x <d y → x ↑d y ≡ y
↑d-right {x} {y} x<y with y ≤d? x
... | yes y≤x = ⊥-elim (x<y y≤x)
... | no _ = refl

postulate
  Choose-↑d : Choose _↑d_
  Choose-Left-↑d : Choose-Left _↑d_ _≤d_

-- ↑d-distr holds without side-conditions

↑d-distr : ∀ z x y 
           → z ↑d (x ↑d y) ≡ (z ↑d x) ↑d (z ↑d y)
↑d-distr z x y with y ≤d? x
↑d-distr z x y | yes y≤x with x ≤d? z 
↑d-distr z x y | yes y≤x | yes x≤z with y ≤d? z
↑d-distr z x y | yes y≤x | yes x≤z | yes y≤z with z ≤d? z
↑d-distr z x y | yes y≤x | yes x≤z | yes y≤z | yes _ = refl
↑d-distr z x y | yes y≤x | yes x≤z | yes y≤z | no z<z = ⊥-elim (z<z ≤d-refl)
↑d-distr z x y | yes y≤x | yes x≤z | no z<y with y ≤d? z
↑d-distr z x y | yes y≤x | yes x≤z | no z<y | yes y≤z = ⊥-elim (z<y y≤z)
↑d-distr z x y | yes y≤x | yes x≤z | no z<y | no _ = ⊥-elim (z<y (≤d-trans y≤x x≤z))
↑d-distr z x y | yes y≤x | no z<x with y ≤d? z
↑d-distr z x y | yes y≤x | no z<x | yes y≤z with z ≤d? x
↑d-distr z x y | yes y≤x | no z<x | yes y≤z | yes z≤x = refl
↑d-distr z x y | yes y≤x | no z<x | yes y≤z | no  x<z = ⊥-elim (z<x (<d→≤d x<z))
↑d-distr z x y | yes y≤x | no z<x | no z<y with y ≤d? x
↑d-distr z x y | yes y≤x | no z<x | no z<y | yes _ = refl
↑d-distr z x y | yes y≤x | no z<x | no z<y | no x>y = ⊥-elim (x>y y≤x)
↑d-distr z x y | no  x<y with y ≤d? z 
↑d-distr z x y | no  x<y | yes y≤z with x ≤d? z
↑d-distr z x y | no  x<y | yes y≤z | yes x≤z with z ≤d? z
↑d-distr z x y | no  x<y | yes y≤z | yes x≤z | yes _ = refl
↑d-distr z x y | no  x<y | yes y≤z | yes x≤z | no z<z = ⊥-elim (z<z ≤d-refl)
↑d-distr z x y | no  x<y | yes y≤z | no z<x = ⊥-elim (z<x (≤d-trans (<d→≤d x<y) y≤z))
↑d-distr z x y | no  x<y | no z<y with x ≤d? z
↑d-distr z x y | no  x<y | no z<y | yes x≤z with y ≤d? z
↑d-distr z x y | no  x<y | no z<y | yes x≤z | yes y≤z = ⊥-elim (z<y y≤z)
↑d-distr z x y | no  x<y | no z<y | yes x≤z | no _ = refl
↑d-distr z x y | no  x<y | no z<y | no z<x with y ≤d? x
↑d-distr z x y | no  x<y | no z<y | no z<x | yes y≤x = ⊥-elim (x<y y≤x)
↑d-distr z x y | no  x<y | no z<y | no z<x | no _ = refl

↑dz : List Elem → List Elem → List Elem → List Elem
↑dz z x y with (z ++ y) ≤d? (z ++ x)
... | yes y≤dx = x
... | no y>dx = y

↑dzc : List Elem → List (List Elem) → List (List Elem) → List (List Elem)
↑dzc z xs ys with (z ++ concat ys) ≤d? (z ++ concat xs)
... | yes y≤dx = xs
... | no y>dx = ys
