module RightSkew where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Function using (_∘_; id)
open import Data.Nat
open import Data.List
open import Data.List.All

open import Relation.Nullary
open import Relation.Binary hiding (NonEmpty)

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Elem
open import List+
open import Prefix
open import MDS
open import Properties.Max

open import Utilities

open import Properties.Max using (maxd-maximum)

open import AlgebraicReasoning.Equality
open import AlgebraicReasoning.Implications 

RightSkew : List Elem → Set
RightSkew x = 
   (∀ n → 0 < n → n < length x 
        → take n x ≤d drop n x)

singleton-RS : ∀ a → RightSkew [ a ]
singleton-RS a zero () _
singleton-RS a (suc n) 1≤n (s≤s ())

private

  data SplitView {A : Set} : ℕ → List A → List A → Set where
     front : ∀ {n} x₁ x₂ y → (eq : n ≡ length x₁) → n < length (x₁ ++ x₂)
             → SplitView n (x₁ ++ x₂) y
     middle : ∀ {n} x y → (eq : n ≡ length x)
              → SplitView n x y
     rear  : ∀ k x y₁ y₂ → (eq : k ≡ length y₁) → 0 < k → k < length (y₁ ++ y₂)
             → SplitView (length x + k) x (y₁ ++ y₂)

  postulate
   splitView : ∀ {A} n (x y : List A) 
               → NonEmpty x
               → n < length (x ++ y) → SplitView n x y
{-
  splitView : ∀ {A} n (x y : List A) 
              → NonEmpty x
              → n < length (x ++ y) → SplitView n x y
  splitView zero ._ y (a ∷ x) n< = front [] (a ∷ x) y refl (s≤s z≤n)
  splitView (suc zero) ._ y (a ∷ []) n< = 
      middle (a ∷ []) y refl
  splitView (suc (suc n)) ._ y (a ∷ []) n< = {!!}
  splitView (suc n) ._ y (a ∷ x) n< = {!!}
-}
 
RightSkew-++ : ∀ {x y} → NonEmpty x → NonEmpty y
               → RightSkew x → RightSkew y
               → x ≤d y → RightSkew (x ++ y)
RightSkew-++ {x} {y} nx ny rx ry x≤y n 0<n n<#xy 
  with splitView n x y nx  n<#xy
RightSkew-++ nx ny rx ry x≤y n 0<n n<#xy | front x₁ x₂ y n=#x₁ n<#x₁x₂ 
  with takeNE n nx 0<n | dropNE n nx n<#x₁x₂ 
... | nx₁ | nx₂
  with rx n 0<n n<#x₁x₂ 
... | x₁≤x₂ rewrite sym (assoc x₁ x₂ y) | n=#x₁
        | take#n x₁ x₂ | take#n x₁ (x₂ ++ y)
        | drop#n x₁ x₂ | drop#n x₁ (x₂ ++ y)
        = (⇐-begin
             x₁ ≤d x₂ ++ y 
           ⇐⟨ ≤d-++→≤d {x₁} {x₂ ++ y} nx₁ (NE-++-l nx₂) ⟩
             x₁ ≤d x₁ ++ x₂ ++ y 
           ⇐⟨ ≤d-trans (≤d→≤d-++ nx₁ nx₂ x₁≤x₂) ⟩
             x₁ ++ x₂ ≤d x₁ ++ x₂ ++ y
           ⇐⟨ subst (λ y₁ → x₁ ++ x₂ ≤d y₁) (sym (assoc x₁ x₂ y)) ⟩
             x₁ ++ x₂ ≤d (x₁ ++ x₂) ++ y
           ⇐⟨ ≤d→≤d-++ {x₁ ++ x₂} {y} nx ny ⟩ 
             x₁ ++ x₂ ≤d y 
           ⇐∎) x≤y
RightSkew-++ nx ny rx ry x≤y n 1≤n n<#xy | middle x y n=#x 
  rewrite n=#x | take#n x y | drop#n x y = x≤y
RightSkew-++ nx ny rx ry x≤y ._ 1≤n n<#xy | rear k x y₁ y₂ k=#y₁ 0<k k<#y
  rewrite take#nk k x (y₁ ++ y₂) | drop#nk k x (y₁ ++ y₂)
  with takeNE k ny 0<k | dropNE k ny k<#y
... | ny₁ | ny₂
  with ry k 0<k k<#y
... | y₁≤y₂
  rewrite k=#y₁ | take#n y₁ y₂ | drop#n y₁ y₂
 = (⇐-begin
      x ++ y₁ ≤d y₂ 
    ⇐⟨ ++-≤d→≤d {x ++ y₁} {y₂} (NE-++-l nx) ny₂ ⟩
      (x ++ y₁) ++ y₂ ≤d y₂ 
    ⇐⟨ subst (λ z → z ≤d y₂) (assoc x y₁ y₂) ⟩
      x ++ y₁ ++ y₂ ≤d y₂ 
    ⇐⟨ (λ leq → ≤d-trans {x ++ y₁ ++ y₂} {y₁ ++ y₂} {y₂} leq 
         (≤d→++-≤d {y₁} {y₂} ny₁ ny₂ y₁≤y₂)) ⟩
      x ++ y₁ ++ y₂ ≤d y₁ ++ y₂ 
    ⇐⟨ ≤d→++-≤d {x} {y₁ ++ y₂} nx ny ⟩ 
      x ≤d y₁ ++ y₂
    ⇐∎) x≤y

prune-either : ∀ {z x₁ x₂} → NonEmpty z → NonEmpty x₁ → NonEmpty x₂
                → x₁ ≤d x₂
                → (z ++ x₁ ≤d z) ⊎ (z ++ x₁ <d z ++ x₁ ++ x₂)
prune-either {z} {x₁} {x₂} nz nx₁ nx₂ x₁≤x₂ with x₁ ≤d? z
... | yes x₁≤z = inj₁ (≥d→≥d-++ nz nx₁ x₁≤z)
... | no z<x₁ = inj₂ (body z<x₁)
  where body : z <d x₁ → z ++ x₁ <d z ++ x₁ ++ x₂
        body = ⇒-begin 
                 z <d x₁ 
               ⇒⟨ <d→++-<d nz nx₁ ⟩
                 z ++ x₁ <d x₁ 
               ⇒⟨ (λ zx₁<x₁ → <d≤d-trans zx₁<x₁ x₁≤x₂) ⟩
                 z ++ x₁ <d x₂ 
               ⇒⟨ <d→<d-++ (NE-++-l nz) nx₂ ⟩ 
                 z ++ x₁ <d (z ++ x₁) ++ x₂ 
               ⇒⟨ subst (λ y → z ++ x₁ <d y) (sym (assoc z x₁ x₂)) ⟩ 
                 z ++ x₁ <d z ++ x₁ ++ x₂ 
               ⇒∎
{-
prune-either : ∀ {z x₁ x₂} → NonEmpty z → NonEmpty x₁ → NonEmpty x₂
               → x₁ ≤d x₂
               → (z ++ x₁ <d z) ⊎ (z ++ x₁ ≤d z ++ x₁ ++ x₂)
prune-either {z} {x₁} {x₂} nz nx₁ nx₂ x₁≤x₂ with z ≤d? x₁
... | no x₁<z = inj₁ (>d→>d-++ nz nx₁ x₁<z)
... | yes z≤x₁ = 
      inj₂ ((⇒-begin 
              z ≤d x₁ 
            ⇒⟨ ≤d→++-≤d nz nx₁ ⟩ 
              z ++ x₁ ≤d x₁ 
            ⇒⟨ (λ zx₁≤x₁ → ≤d-trans zx₁≤x₁ x₁≤x₂) ⟩ 
              z ++ x₁ ≤d x₂ 
            ⇒⟨ ≤d→≤d-++ (NE-++-l nz) nx₂ ⟩ 
              z ++ x₁ ≤d (z ++ x₁) ++ x₂ 
            ⇒⟨ subst (λ y → z ++ x₁ ≤d y) (sym (assoc z x₁ x₂)) ⟩ 
              z ++ x₁ ≤d z ++ x₁ ++ x₂ 
            ⇒∎
           ) z≤x₁) -}

two-in-three : ∀ {z x₁ x₂} → NonEmpty z → NonEmpty x₁ → NonEmpty x₂
               → x₁ ≤d x₂
               → z ↑d ((z ++ x₁) ↑d (z ++ x₁ ++ x₂)) 
                 ≡ z ↑d (z ++ x₁ ++ x₂)
two-in-three {z} {x₁} {x₂} nz nx₁ nx₂ x₁≤x₂ = body
  where pe : (z ++ x₁ ≤d z) ⊎ (z ++ x₁ <d z ++ x₁ ++ x₂)
        pe = prune-either nz nx₁ nx₂ x₁≤x₂

        body₁ : z ++ x₁ ≤d z → z ↑d ((z ++ x₁) ↑d (z ++ x₁ ++ x₂)) ≡ z ↑d (z ++ x₁ ++ x₂)
        body₁ zx₁≤z with (z ++ x₁ ++ x₂) ≤d? (z ++ x₁) 
        ... | no _ = refl
        ... | yes zx₁x₂≤zx₁ with (z ++ x₁) ≤d? z 
        ...     | no z<zx₁ = ⊥-elim (z<zx₁ zx₁≤z)
        ...     | yes _ with  (z ++ x₁ ++ x₂) ≤d? z
        ...              | yes _ = refl
        ...              | no z<zx₁x₂ = ⊥-elim (z<zx₁x₂ (≤d-trans zx₁x₂≤zx₁ zx₁≤z))

        body₂ : z ++ x₁ <d z ++ x₁ ++ x₂ 
                → z ↑d ((z ++ x₁) ↑d (z ++ x₁ ++ x₂)) ≡ z ↑d (z ++ x₁ ++ x₂)
        body₂ zx₁<zx₁x₂ with (z ++ x₁ ++ x₂) ≤d? (z ++ x₁)
        ... | no _ = refl
        ... | yes zx₁x₂≤zx₁ = ⊥-elim (zx₁<zx₁x₂ zx₁x₂≤zx₁)

        body : z ↑d ((z ++ x₁) ↑d (z ++ x₁ ++ x₂)) ≡ z ↑d (z ++ x₁ ++ x₂)
        body with pe
        ... | inj₁ zx₁≤z = body₁ zx₁≤z
        ... | inj₂ zx₁<zx₁x₂ = body₂ zx₁<zx₁x₂

RightSkewExt : List Elem → List Elem → Set
RightSkewExt y x = 
   (∀ n → NonEmpty (y ++ take n x) → (suc n) ≤ length x 
        → (y ++ take n x) ≤d drop n x)

-- I've taken care to ensure that rightskew-prefix-cancel is true
-- even when y is empty. But it turned out to be not necessary.

rightskew-prefix-cancel :
    ∀ z y x → NonEmpty z → NonEmpty y
    → RightSkewExt y x
    → z ↑d maxd (map⁺ (_++_ (z ++ y)) (prefixes x))
      ≡ z ↑d (z ++ y ++ x)
rightskew-prefix-cancel z y [] nz ny rx rewrite assoc z y [] = refl
rightskew-prefix-cancel z y (a ∷ x) nz ny rx = body
 where 
  aux : ∀ {A : Set} (z y : List A) a x 
        → (z ++ y) ++ a ∷ x ≡ (z ++ y ++ a ∷ []) ++ x
  aux [] y a x rewrite assoc y [ a ] x = refl
  aux (b ∷ z) y a x rewrite aux z y a x = refl

  body : z ↑d maxd (map⁺ (_++_ (z ++ y)) (prefixes (a ∷ x)))
         ≡ z ↑d (z ++ y ++ a ∷ x)
  body rewrite r-id-++-[] (z ++ y) 
             | map⁺-functor (_++_ (z ++ y)) (_∷_ a) (prefixes x)
             | map⁺-cong (λ w → (z ++ y) ++ a ∷ w) 
                     (λ w → (z ++ y ++ [ a ]) ++ w) (aux z y a) (prefixes x)
   = ≡-begin
       z ↑d ((z ++ y) ↑d
        maxd (map⁺ (_++_ (z ++ y ++ a ∷ [])) (prefixes x)))
     ≡⟨ ↑d-distr z (z ++ y) (maxd (map⁺ (_++_ (z ++ y ++ a ∷ [])) (prefixes x)))
        {- dr₁ -} {- nz (NE-++-l nz) ne-mzy -} ⟩ 
       (z ↑d (z ++ y)) ↑d
         (z ↑d maxd (map⁺ (_++_ (z ++ y ++ a ∷ [])) (prefixes x)))
     ≡⟨ cong (λ w → (z ↑d (z ++ y)) ↑d w) 
         (rightskew-prefix-cancel z (y ++ [ a ]) x nz (NE-++-l ny) rs-ext) ⟩ 
       (z ↑d (z ++ y)) ↑d (z ↑d (z ++ (y ++ a ∷ []) ++ x))
     ≡⟨ cong (λ w → (z ↑d (z ++ y)) ↑d (z ↑d (z ++ w))) 
         (sym (assoc y [ a ] x)) ⟩ 
       (z ↑d (z ++ y)) ↑d (z ↑d (z ++ y ++ a ∷ x))
     ≡⟨ sym (↑d-distr z (z ++ y) (z ++ y ++ a ∷ x) 
             {- dr₂ -} {- nz (NE-++-l nz) (NE-++-l nz) -}) ⟩
       z ↑d ((z ++ y) ↑d (z ++ y ++ a ∷ x)) 
     ≡⟨ ↑d-assoc z (z ++ y) (z ++ y ++ a ∷ x) ⟩ 
       (z ↑d (z ++ y)) ↑d (z ++ y ++ a ∷ x) 
     ≡⟨ two-in-three' ⟩
       z ↑d (z ++ y ++ a ∷ x)
     ≡∎
   where {- ne-mzy : NonEmpty (maxd (map⁺ (_++_ (z ++ y ++ a ∷ [])) (prefixes x)))
         ne-mzy = maxd-pred NonEmpty (map⁺ (_++_ (z ++ y ++ a ∷ [])) (prefixes x)) 
                   (map⁺-pred (_++_ (z ++ y ++ a ∷ [])) NonEmpty ne (prefixes x))
            where ne : ∀ x → NonEmpty ((z ++ y ++ a ∷ []) ++ x)
                  ne x = NE-++-l (NE-++-l nz) -}
         y≤ax : y ≤d (a ∷ x)
         y≤ax with rx | ny 
         y≤ax | rx | ny with y
         y≤ax | rx | () | []
         y≤ax | rx | ny | b ∷ y' = by≤ax
           where by≤ax :  b ∷ y' ≤d a ∷ x
                 by≤ax with rx 0 (b ∷ _) (s≤s z≤n) 
                 ... | p rewrite r-id-++-[] y' = p

         zyax∈ : (z ++ y ++ a ∷ x) ∈ map⁺ (_++_ (z ++ y ++ a ∷ [])) (prefixes x)
         zyax∈ rewrite assoc z y (a ∷ x) 
                     | assoc (z ++ y) [ a ] x 
                     | sym (assoc z y [ a ]) = 
           map⁺-∈ (_++_ (z ++ y ++ a ∷ [])) (⊑-prefixes {x = x} ⊑-refl)

         zyax≤w : z ++ y ++ a ∷ x ≤d maxd (map⁺ (_++_ (z ++ y ++ a ∷ [])) (prefixes x))
         zyax≤w = maxd-maximum (map⁺ (_++_ (z ++ y ++ a ∷ [])) (prefixes x)) zyax∈

         two-in-three' : (z ↑d (z ++ y)) ↑d (z ++ y ++ a ∷ x) 
                         ≡ z ↑d (z ++ y ++ a ∷ x) 
         two-in-three' with y≤ax
         ... | y≤ax rewrite sym (↑d-assoc z (z ++ y) (z ++ y ++ a ∷ x)) = 
           two-in-three nz ny (a ∷ x) y≤ax

         rs-ext : RightSkewExt (y ++ [ a ]) x
         rs-ext n ne rb rewrite sym (assoc y [ a ] (take n x)) =
           rx (suc n) ne (s≤s rb)

rightskew-prefix :
    ∀ z x → NonEmpty z
    → RightSkew x
    → maxd (map⁺ (_++_ z) (prefixes x)) ≡ z ↑d (z ++ x)
rightskew-prefix z [] nz rx rewrite r-id-++-[] z | ↑d-idem z = refl
rightskew-prefix z (a ∷ x) nz rx rewrite r-id-++-[] z = body
  where aux : ∀ {A : Set} (z : List A) a x 
              → z ++ a ∷ x ≡ (z ++ a ∷ []) ++ x
        aux [] a x = refl
        aux (b ∷ z) a x rewrite aux z a x = refl

        body : z ↑d maxd (map⁺ (_++_ z) (map⁺ (_∷_ a) (prefixes x)))
              ≡ z ↑d (z ++ a ∷ x)
        body rewrite
                map⁺-functor (_++_ z) (_∷_ a) (prefixes x)
              | map⁺-cong (λ w → z ++ a ∷ w) (λ w → (z ++ [ a ]) ++ w)
                      (aux z a) (prefixes x)
           = rightskew-prefix-cancel z [ a ] x nz (a ∷ _) rx' 
         where rx' :  ∀ n → NonEmpty (a ∷ take n x) →
                      suc n ≤ foldr (λ _ → suc) 0 x → a ∷ take n x ≤d drop n x
               rx' n _ leq = rx (suc n) (s≤s z≤n) (s≤s leq)

rightskew-discrete :
  ∀ z xs 
  → NonEmpty z → All RightSkew xs
  → maxd (map⁺ (_++_ z) (prefixes (concat xs)))
    ≡ maxd (map⁺ ((_++_ z) ∘ concat) (prefixes xs))
rightskew-discrete z [] _ _ = refl
rightskew-discrete z (x ∷ xs) nz (rx ∷ rs) = 
  ≡-begin 
     maxd (map⁺ (_++_ z) (prefixes (x ++ concat xs))) 
  ≡⟨ maxd-prefix-++ (_++_ z) x (concat xs) ⟩ 
    maxd (map⁺ (_++_ z) (prefixes x)) ↑d
      maxd (map⁺ (_++_ z ∘ _++_ x) (prefixes (concat xs)))
  ≡⟨ cong (λ w → w ↑d maxd (map⁺ (_++_ z ∘ _++_ x) (prefixes (concat xs)))) 
      (rightskew-prefix z x nz rx) ⟩ 
    (z ↑d (z ++ x)) ↑d
    maxd (map⁺ (_++_ z ∘ _++_ x) (prefixes (concat xs)))
  ≡⟨ cong (λ w → (z ↑d (z ++ x)) ↑d maxd w) 
      (map⁺-cong (_++_ z ∘ _++_ x) (_++_ (z ++ x)) (λ y → assoc z x y) 
        (prefixes (concat xs))) ⟩ 
    (z ↑d (z ++ x)) ↑d
    maxd (map⁺ (_++_ (z ++ x)) (prefixes (concat xs)))
  ≡⟨ cong (λ w → (z ↑d (z ++ x)) ↑d w) 
     (rightskew-discrete (z ++ x) xs (NE-++-l nz) rs) ⟩ 
    (z ↑d (z ++ x)) ↑d
    maxd (map⁺ (_++_ (z ++ x) ∘ concat) (prefixes xs))
  ≡⟨ sym (↑d-assoc z (z ++ x) _) ⟩ 
    z ↑d ((z ++ x) ↑d maxd (map⁺ (_++_ (z ++ x) ∘ concat) (prefixes xs)))
  ≡⟨ cong (λ w → z ↑d ((z ++ x) ↑d maxd w)) eq₁ ⟩ 
    z ↑d ((z ++ x) ↑d
               maxd (map⁺ (_++_ z ∘ concat) (map⁺ (_∷_ x) (prefixes xs))))
  ≡⟨ sym eq₂ ⟩
    maxd (map⁺ (_++_ z ∘ concat) (prefixes (x ∷ xs))) 
  ≡∎
 where eq₁ : map⁺ (_++_ (z ++ x) ∘ concat) (prefixes xs)
             ≡ map⁺ (_++_ z ∘ concat) (map⁺ (_∷_ x) (prefixes xs))
       eq₁ = sym 
        (≡-begin
           map⁺ (_++_ z ∘ concat) (map⁺ (_∷_ x) (prefixes xs)) 
         ≡⟨ map⁺-functor (_++_ z ∘ concat) (_∷_ x) (prefixes xs) ⟩ 
           map⁺ (_++_ z ∘ concat ∘ _∷_ x) (prefixes xs)
         ≡⟨ map⁺-cong (_++_ z ∘ concat ∘ _∷_ x) (_++_ (z ++ x) ∘ concat)
            (λ xs' → assoc z x (concat xs')) (prefixes xs) ⟩ 
           map⁺ (_++_ (z ++ x) ∘ concat) (prefixes xs) 
         ≡∎)
       eq₂ : maxd (map⁺ (_++_ z ∘ concat) (prefixes (x ∷ xs))) 
             ≡ z ↑d ((z ++ x) ↑d
               maxd (map⁺ (_++_ z ∘ concat) (map⁺ (_∷_ x) (prefixes xs))))
       eq₂ rewrite r-id-++-[] z with xs
       ... | [] rewrite (r-id-++-[] x) | ↑d-idem (z ++ x) = refl
       ... | y ∷ xs rewrite (r-id-++-[] x) 
                    | ↑d-assoc (z ++ x) (z ++ x)
                         (maxd (map⁺ (_++_ z ∘ concat) 
                                 (map⁺ (_∷_ x) (map⁺ (_∷_ y) (prefixes xs)))))
                    | ↑d-idem (z ++ x)
               = refl

rightskew-discrete' :
  ∀ z xs 
  → NonEmpty z → All RightSkew xs
  → max-with (↑dz z) (prefixes (concat xs))
     ≡ concat (max-with (↑dzc z) (prefixes xs))
rightskew-discrete' z xs nz rs 
  with rightskew-discrete z xs nz rs
... | eq rewrite max-d-dz z (prefixes (concat xs))
               | max-d-dzc z (prefixes xs) = ++-inj z eq
