module Elem.Maximum where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary

open import Relation.Binary.PropositionalEquality

open import Utilities using (≤-refl; ≤-trans; <→≤; tri)

open import Elem.Core
open import Elem.Preceq

[]-↑≼-id : ∀ x → [] ↑≼ x ≡ x
[]-↑≼-id x with we? [] | we? x
... | yes ⊠[] | _ = ⊥-elim (L-positive ⊠[])
... | no _ | no _ with x ≤w? [] 
...               | yes x=w[] rewrite width-[] x=w[] = refl
...               | no _  = refl
[]-↑≼-id x | no _ | yes _ = refl

↑≼-max-l : ∀ x y → x ≼ (x ↑≼ y)
↑≼-max-l x y with we? x | we? y
↑≼-max-l x y | no □x | no □y with y ≤w? x
↑≼-max-l x y | no □x | no □y | no x<wy = ≼-initial □x □y (<→≤ x<wy)
↑≼-max-l x y | no □x | no □y | yes _ = ≼-refl 
↑≼-max-l x y | no □x | yes ⊠y = ≼-triv □x ⊠y 
↑≼-max-l x y | yes ⊠x | no □y = ≼-refl 
↑≼-max-l x y | yes ⊠x | yes ⊠y with y ≤d? x
↑≼-max-l x y | yes ⊠x | yes ⊠y | no x<dy = ≼-density ⊠x ⊠y (<d→≤d x<dy) 
↑≼-max-l x y | yes ⊠x | yes ⊠y | yes _ = ≼-refl

↑≼-we₁ : ∀ {x y} → we x → we (x ↑≼ y)
↑≼-we₁ {x} {y} ⊠x with we? x | we? y
... | no □x | _ = ⊥-elim (□x ⊠x)
... | yes _ | no _ = ⊠x
... | yes _ | yes ⊠y with y ≤d? x
...   | yes _ = ⊠x
...   | no _ = ⊠y

↑≼-we₂ : ∀ {x y} → we y → we (x ↑≼ y)
↑≼-we₂ {x} {y} ⊠y with we? x | we? y 
... | _ | no □y = ⊥-elim (□y ⊠y)
... | no _ | yes _ = ⊠y
... | yes ⊠x | yes _ with y ≤d? x
...    | yes _ = ⊠x
...    | no _ = ⊠y

↑≼-assoc : ∀ {x y z} → x ↑≼ (y ↑≼ z) ≡ (x ↑≼ y) ↑≼ z
↑≼-assoc {x}{y}{z} with we? y | we? z
↑≼-assoc {x}{y}{z} | no _ | no _ with z ≤w? y 
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ with we? z 
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ with we? x 
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | no _ with y ≤w? x
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | no _ | no _ with z ≤w? x
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | no _ | no _ | no _ with we? y 
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ with x ≤w? y 
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ with z ≤w? y 
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ = refl
↑≼-assoc {x}{y}{z} | no _ | no _ | no y<z | no _ | no _ | no _ | no _ | no _ | no _ | yes y≤z = ⊥-elim (y<z y≤z)
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | yes _ with z ≤w? y
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | yes _ | no _ = refl
↑≼-assoc {x}{y}{z} | no _ | no _ | no y<z | no _ | no _ | no _ | no _ | no _ | yes _ | yes y≤z = ⊥-elim (y<z y≤z)
↑≼-assoc {x}{y}{z} | no □ | no _ | no _ | no _ | no _ | no _ | no _ | yes ⊠ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | no _ | no _ | no y<z | no _ | no _ | no x<y | yes z≤x = ⊥-elim (x<y (≤-trans (<→≤ y<z) z≤x))
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | no _ | yes _ with we? x
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | no _ | yes _ | no _ with z ≤w? x 
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | no _ | yes _ | no _ | no _ = refl
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | no _ | yes _ | no _ | yes _ = refl
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | no □ | yes _ | yes ⊠ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | yes _ with we? x 
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | yes ⊠ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | no _ | no _ | no _ | no _ | yes _ | yes _ = refl
↑≼-assoc {x}{y}{z} | no _ | no □ | no _ | yes ⊠ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | no _ | no _ | yes _ with we? y 
↑≼-assoc {x}{y}{z} | no _ | no _ | yes _ | no _ with we? x 
↑≼-assoc {x}{y}{z} | no _ | no _ | yes _ | no _ | no _ with y ≤w? x
↑≼-assoc {x}{y}{z} | no _ | no _ | yes _ | no _ | no _ | no _ with we? y 
↑≼-assoc {x}{y}{z} | no _ | no _ | yes _ | no _ | no _ | no _ | no _ with z ≤w? y 
↑≼-assoc {x}{y}{z} | no _ | no _ | yes z≤y | no _ | no _ | no _ | no _ | no y<z = ⊥-elim (y<z z≤y)
↑≼-assoc {x}{y}{z} | no _ | no _ | yes _ | no _ | no _ | no _ | no _ | yes _ = refl
↑≼-assoc {x}{y}{z} | no □ | no _ | yes _ | no _ | no _ | no _ | yes ⊠ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | no _ | no _ | yes _ | no _ | no _ | yes _ with we? x
↑≼-assoc {x}{y}{z} | no _ | no _ | yes _ | no _ | no _ | yes _ | no _ with z ≤w? x
↑≼-assoc {x}{y}{z} | no _ | no _ | yes z≤y | no _ | no _ | yes y≤x | no _ | no x<z = ⊥-elim (x<z (≤-trans z≤y y≤x))
↑≼-assoc {x}{y}{z} | no _ | no _ | yes _ | no _ | no _ | yes _ | no _ | yes _ = refl
↑≼-assoc {x}{y}{z} | no _ | no _ | yes _ | no _ | no □ | yes _ | yes ⊠ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | no _ | no _ | yes _ | no _ | yes _ with we? x
↑≼-assoc {x}{y}{z} | no _ | no _ | yes _ | no _ | yes ⊠ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | no _ | no _ | yes _ | no _ | yes _ | yes _ = refl
↑≼-assoc {x}{y}{z} | no □ | no _ | yes _ | yes ⊠ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | no _ | yes _ with we? x
↑≼-assoc {x}{y}{z} | no _ | yes _ | no _ with y ≤w? x 
↑≼-assoc {x}{y}{z} | no _ | yes _ | no _ | no _ with we? y 
↑≼-assoc {x}{y}{z} | no _ | yes _ | no _ | no _ | no _ with we? z
↑≼-assoc {x}{y}{z} | no _ | yes ⊠ | no _ | no _ | no _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | no _ | yes _ | no _ | no _ | no _ | yes _ = refl
↑≼-assoc {x}{y}{z} | no □ | yes _ | no _ | no _ | yes ⊠ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | no _ | yes _ | no _ | yes _ with we? z
↑≼-assoc {x}{y}{z} | no _ | yes ⊠ | no _ | yes _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | no _ | yes _ | no _ | yes _ | yes _ with we? x
↑≼-assoc {x}{y}{z} | no _ | yes _ | no _ | yes _ | yes _ | no _ = refl
↑≼-assoc {x}{y}{z} | no _ | yes _ | no □ | yes _ | yes _ | yes ⊠ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | no _ | yes _ | yes _ with we? z
↑≼-assoc {x}{y}{z} | no _ | yes ⊠ | yes _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | no _ | yes _ | yes _ | yes _ with we? x
↑≼-assoc {x}{y}{z} | no _ | yes _ | yes ⊠ | yes _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | no _ | yes _ | yes _ | yes _ | yes _ = refl
↑≼-assoc {x}{y}{z} | yes _ | no _ with we? y
↑≼-assoc {x}{y}{z} | yes _ | no _ | yes _ with we? x
↑≼-assoc {x}{y}{z} | yes _ | no _ | yes _ | no _ with we? y
↑≼-assoc {x}{y}{z} | yes ⊠ | no _ | yes _ | no _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | yes _ | no _ | yes _ | no _ | yes _ = refl
↑≼-assoc {x}{y}{z} | yes _ | no _ | yes _ | yes _ with y ≤d? x 
↑≼-assoc {x}{y}{z} | yes _ | no _ | yes _ | yes _ | no _ with we? y
↑≼-assoc {x}{y}{z} | yes ⊠ | no _ | yes _ | yes _ | no _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | yes _ | no _ | yes _ | yes _ | no _ | yes _ = refl
↑≼-assoc {x}{y}{z} | yes _ | no _ | yes _ | yes _ | yes _ with we? x
↑≼-assoc {x}{y}{z} | yes _ | no _ | yes _ | yes ⊠ | yes _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | yes _ | no _ | yes _ | yes _ | yes _ | yes _ = refl
↑≼-assoc {x}{y}{z} | yes ⊠ | no _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | yes _ | yes _ with z ≤d? y
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no _ with we? x
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no _ | no _ with we? y 
↑≼-assoc {x}{y}{z} | yes ⊠ | yes _ | no _ | no _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no _ | no _ | yes _ with we? z
↑≼-assoc {x}{y}{z} | yes _ | yes ⊠ | no _ | no _ | yes _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no _ | no _ | yes _ | yes _ with z ≤d? y
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no _ | no _ | yes _ | yes _ | no _ = refl
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no y<z | no _ | yes _ | yes _ | yes z≤y = ⊥-elim (y<z z≤y)
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no _ | yes _ with y ≤d? x 
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no _ | yes _ | no _ with we? y 
↑≼-assoc {x}{y}{z} | yes ⊠ | yes _ | no _ | yes _ | no _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no _ | yes _ | no _ | yes _ with we? z
↑≼-assoc {x}{y}{z} | yes _ | yes ⊠ | no _ | yes _ | no _ | yes _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no _ | yes _ | no _ | yes _ | yes _ with z ≤d? y 
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no _ | yes _ | no _ | yes _ | yes _ | no _ with z ≤d? x
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no _ | yes _ | no _ | yes _ | yes _ | no _ | no _ = refl
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no y<z | yes _ | no x<y | yes _ | yes _ | no _ | yes z≤x = 
  ⊥-elim ((<d-trans x<y y<z) z≤x)
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no y<z | yes _ | no _ | yes _ | yes _ | yes z≤y = ⊥-elim (y<z z≤y)
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no _ | yes _ | yes _ with we? z
↑≼-assoc {x}{y}{z} | yes _ | yes ⊠ | no _ | yes _ | yes _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no _ | yes _ | yes _ | yes _ with we? x
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no _ | yes ⊠ | yes _ | yes _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | yes _ | yes _ | no _ | yes _ | yes _ | yes _ | yes _ = refl
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes _ with we? x 
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes _ | no _ with we? y
↑≼-assoc {x}{y}{z} | yes ⊠ | yes _ | yes _ | no _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes _ | no _ | yes _ with z ≤d? y 
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes z≤y | no _ | yes _ | no y<z = ⊥-elim (y<z z≤y)
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes _ | no _ | yes _ | yes _ = refl
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes _ | yes _ with we? y
↑≼-assoc {x}{y}{z} | yes ⊠ | yes _ | yes _ | yes _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes _ | yes _ | yes _ with y ≤d? x
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes _ | yes _ | yes _ | no _ with we? y
↑≼-assoc {x}{y}{z} | yes ⊠ | yes _ | yes _ | yes _ | yes _ | no _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes _ | yes _ | yes _ | no _ | yes _ with z ≤d? y
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes z≤y | yes _ | yes _ | no _ | yes _ | no y<z = ⊥-elim (y<z z≤y)
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes _ | yes _ | yes _ | no _ | yes _ | yes _ = refl
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes _ | yes _ | yes _ | yes _ with we? x
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes _ | yes ⊠ | yes _ | yes _ | no □ = ⊥-elim (□ ⊠)
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes _ | yes _ | yes _ | yes _ | yes _ with z ≤d? x
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes z≤y | yes _ | yes _ | yes y≤x | yes _ | no x<z = ⊥-elim (x<z (≤d-trans z≤y y≤x))
↑≼-assoc {x}{y}{z} | yes _ | yes _ | yes _ | yes _ | yes _ | yes _ | yes _ | yes _ = refl


↑≼-idem : ∀ x → x ↑≼ x ≡ x
↑≼-idem x with we? x
↑≼-idem x | no _ with x ≤w? x
↑≼-idem x | no _ | no p = ⊥-elim (p ≤-refl)
↑≼-idem x | no _ | yes _ = refl
↑≼-idem x | yes _ with x ≤d? x
↑≼-idem x | yes _ | no p = ⊥-elim (p ≤d-refl)
↑≼-idem x | yes _ | yes p = refl

↑≼-either' : ∀ x y → 
  ((x ↑≼ y ≡ x) × (y ≼ x)) ⊎ 
  ((x ↑≼ y ≡ y) × (x ≺ y))
↑≼-either' x y with we? x | we? y 
↑≼-either' x y | no _ | no _ with y ≤w? x 
↑≼-either' x y | no □x | no □y | no x<y = inj₂ (refl , (≼-initial □x □y (<→≤ x<y)) , ¬y≼x) 
  where ¬y≼x : ¬ (y ≼ x)
        ¬y≼x (≼-initial _ _ y≤x) = x<y y≤x
        ¬y≼x (≼-triv _ ⊠x) = □x ⊠x
        ¬y≼x (≼-density ⊠y _ _) = □y ⊠y 
↑≼-either' x y | no □x | no □y | yes y≤x = inj₁ (refl , ≼-initial □y □x y≤x) 
↑≼-either' x y | no □x | yes ⊠y = inj₂ (refl , ≼-triv □x ⊠y , ¬y≼x) 
  where ¬y≼x : ¬ (y ≼ x)
        ¬y≼x (≼-initial □y _ _) = □y ⊠y
        ¬y≼x (≼-triv _ ⊠x) = □x ⊠x
        ¬y≼x (≼-density _ ⊠x _) = □x ⊠x
↑≼-either' x y | yes ⊠x | no □y = inj₁ (refl , ≼-triv □y ⊠x)
↑≼-either' x y | yes _ | yes _ with y ≤d? x
↑≼-either' x y | yes ⊠x | yes ⊠y | no x<y = inj₂ (refl , ≼-density ⊠x ⊠y (<d→≤d x<y) , ¬y≼x)
  where ¬y≼x : ¬ (y ≼ x)
        ¬y≼x (≼-initial □y _ _) = □y ⊠y
        ¬y≼x (≼-triv □y _) = □y ⊠y
        ¬y≼x (≼-density _ _ y≤x) = x<y y≤x
↑≼-either' x y | yes ⊠x | yes ⊠y | yes y≤x  = inj₁ (refl , ≼-density ⊠y ⊠x y≤x)

Choose-Left-↑≼ : Choose-Left _↑≼_ _≼_
Choose-Left-↑≼ = ↑≼-either'

↑≼-either : ∀ x y → (x ↑≼ y ≡ x) ⊎ (x ↑≼ y ≡ y)
↑≼-either x y with ↑≼-either' x y
... | inj₁ (eq , _) = inj₁ eq
... | inj₂ (eq , _) = inj₂ eq

↑≼-pred : (P : List Elem → Set) 
          → ∀ x y → (P x × P y) → P (x ↑≼ y)
↑≼-pred P x y (px , py) with ↑≼-either x y
↑≼-pred P x y (px , py) | inj₁ eq rewrite eq = px 
↑≼-pred P x y (px , py) | inj₂ eq rewrite eq = py 

↑≼-GC-→ : ∀ {x y z} → (x ↑≼ y) ≼ z → (x ≼ z × y ≼ z)
↑≼-GC-→ {x} {y} {z} ≼z with ↑≼-either' x y
... | inj₁ (eq , y≼x)     rewrite eq = ≼z , ≼-trans y≼x ≼z
... | inj₂ (eq , x≼y , _) rewrite eq = ≼-trans x≼y ≼z , ≼z

≺-max : ∀ {x y z} → (x ↑≼ y) ≺ z → (x ≺ z × y ≺ z)
≺-max {x} {y} {z} (x⊔y≼z , ¬z≼x⊔y) with ↑≼-either' x y
≺-max {x} {y} {z} (x≼z , ¬z≼x) | inj₁ (eq , y≼x) rewrite eq = 
   (x≼z , ¬z≼x) , ≼-trans y≼x x≼z , λ z≼y → ¬z≼x (≼-trans z≼y y≼x)
≺-max {x} {y} {z} (y≼z , ¬z≼y) | inj₂ (eq , x≼y , _) rewrite eq = 
   (≼-trans x≼y y≼z , λ z≼x → ¬z≼y (≼-trans z≼x x≼y)) , y≼z , ¬z≼y

