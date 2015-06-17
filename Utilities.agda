module Utilities where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.List
open import Data.List.All
open import Relation.Nullary

open import Relation.Binary.PropositionalEquality hiding ([_])
import AlgebraicReasoning.MonoPreorderReasoning as MPR

_╳_ : ∀ {A B C D : Set}
      → (A → B) → (C → D) → (A × C) → (B × D)
(f ╳ g) (a , c) = f a , g c

⟨_,_⟩ : ∀ {A B C : Set}
      → (A → B) → (A → C) → A → (B × C)
⟨ f , g ⟩ a = f a , g a

assoc : ∀ {A : Set} (xs ys zs : List A)
                  → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc []       ys zs = refl
assoc (x ∷ xs) ys zs = cong (_∷_ x) (assoc xs ys zs)

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc m} = s≤s ≤-refl

≤-refl' : ∀ {m n} → m ≡ n → m ≤ n
≤-refl' refl = ≤-refl

≥-refl' : ∀ {m n} → m ≡ n → m ≥ n
≥-refl' refl = ≤-refl

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)

≥-trans : ∀ {x y z} → x ≥ y → y ≥ z → x ≥ z
≥-trans y≤x z≤y = ≤-trans z≤y y≤x

<→≤ : ∀ {m n} → ¬ (n ≤ m) → m ≤ n
<→≤ {zero} _ = z≤n
<→≤ {suc m} {zero} 1+m<0 = ⊥-elim (1+m<0 z≤n)
<→≤ {suc m} {suc n} 1+m<1+n = s≤s (<→≤ (λ n≤m → 1+m<1+n (s≤s n≤m)))

module ≤-reasoning = MPR.Mono _≤_ ≤-refl ≤-trans
  renaming (begin_ to ≤-begin_ ; _∼⟨_⟩_ to _≤⟨_⟩_ ; _∎ to _≤∎)

module ≥-reasoning = MPR.Mono _≥_ ≤-refl ≥-trans
  renaming (begin_ to ≥-begin_ ; _∼⟨_⟩_ to _≥⟨_⟩_ ; _∎ to _≥∎)

tri : ∀ {x} y {z} → x ≤ z → x ≤ y ⊎ y ≤ z
tri {x} y {z} x≤z with x ≤? y
tri y x≤z | yes x≤y = inj₁ x≤y
tri y x≤z | no y<x = inj₂ (≤-trans (<→≤ y<x) x≤z)

r-id-++-[] : ∀ {A : Set} (x : List A) → x ++ [] ≡ x
r-id-++-[] [] = refl
r-id-++-[] (a ∷ x) rewrite r-id-++-[] x = refl

∷-inj : ∀ {A : Set} (a : A) {x y : List A} →
          _≡_ {_} {List A} (a ∷ x) (a ∷ y) → x ≡ y
∷-inj a refl = refl

++-inj : ∀ {A : Set} z {x y : List A} → z ++ x ≡ z ++ y → x ≡ y
++-inj [] eq = eq
++-inj (a ∷ z) eq = ++-inj z (∷-inj a eq)

postulate
 r-zero-++[] : ∀ {A : Set} {x : List A} → x ++ [] ≡ [] → x ≡ []
 m-zero-++[] : ∀ {A : Set} (x y z : List A) → x ++ y ++ z ≡ [] → y ≡ []

contrapositive : ∀ {P Q : Set} → (P → Q) → ¬ Q → ¬ P
contrapositive f ¬q p = ¬q (f p)

contrapositive' : ∀ {P Q : Set} → (P → ¬ Q) → Q → ¬ P
contrapositive' f q p = f p q

data SnocWF {A} : List A → Set where
  [] : SnocWF []
  ∷ʳ-wf : ∀ xs → SnocWF xs → (x : A) → SnocWF (xs ++ [ x ])

cons-snocWF : ∀ {A} (x : A) {xs} → SnocWF xs → SnocWF (x ∷ xs)
cons-snocWF x [] = ∷ʳ-wf _ [] x
cons-snocWF x (∷ʳ-wf _ xs y) = ∷ʳ-wf _ (cons-snocWF x xs) y

snocWF :  ∀ {A} (xs : List A) → SnocWF xs
snocWF [] = []
snocWF (x ∷ xs) = cons-snocWF x (snocWF xs)

data Adj {A} (R : A → A → Set) : List A → Set where
  [] : Adj R []
  [·] : ∀ {a} → Adj R [ a ]
  _∷_ : ∀ {a b x} → R a b → Adj R (b ∷ x) → Adj R (a ∷ b ∷ x)

Adj-tl : ∀ {A} {a : A} {x R} → Adj R (a ∷ x) → Adj R x
Adj-tl [·] = []
Adj-tl (_ ∷ tl) = tl

Adj-init : ∀ {A} {a : A} {x R} → Adj R (x ++ [ a ]) → Adj R x
Adj-init {x = []} _ = []
Adj-init {x = b ∷ []} (_ ∷ _) = [·]
Adj-init {x = b ∷ c ∷ x} (bRc ∷ adj) = bRc ∷ Adj-init adj

Adj-last : ∀ {A} {a b : A} x {R} → Adj R ((x ++ [ a ]) ++ [ b ]) → R a b
Adj-last [] (aRb ∷ _) = aRb
Adj-last (c ∷ []) (_ ∷ aRb ∷ _) = aRb
Adj-last (c ∷ d ∷ x) (_ ∷ adj) = Adj-last (d ∷ x) adj

All-init : ∀ {A : Set} {P : A → Set} {x a}
           → All P (x ++ [ a ]) → All P x
All-init {x = []} _ = []
All-init {x = a ∷ x} (pa ∷ px) = pa ∷ All-init px

All-last : ∀ {A : Set} {P : A → Set} x {a}
           → All P (x ++ [ a ]) → P a
All-last [] (pa ∷ _) = pa
All-last (a ∷ x) (pa ∷ px) = All-last x px

infixr 5 _∷_

data NonEmpty {A} : List A → Set where
  _∷_ : ∀ a x → NonEmpty (a ∷ x)

NE-++-l : ∀ {A} {x y : List A} → NonEmpty x → NonEmpty (x ++ y)
NE-++-l {A} {[]} ()
NE-++-l {A} {a ∷ x} NEx = a ∷ _ 

∷-≡-hd-tl : ∀ {A : Set} {a b : A} {x y : List A} 
          → _≡_ {_} {List A} (a ∷ x) (b ∷ y) → a ≡ b × x ≡ y
∷-≡-hd-tl refl = refl , refl

NE-concat-[] : ∀ {A : Set} {xs : List (List A)}
               → All NonEmpty xs
               → concat xs ≡ [] → xs ≡ []
NE-concat-[] [] _ = refl
NE-concat-[] ((_ ∷ _) ∷ _) ()

concat-snoc : ∀ {A : Set} (xs : List (List A)) → (x : List A)
              → concat (xs ++ [ x ]) ≡ concat xs ++ x
concat-snoc [] x = r-id-++-[] x
concat-snoc (y ∷ xs) x 
  rewrite sym (assoc y (concat xs) x) 
        | concat-snoc xs x = refl

foldr-++ : ∀ {A B : Set} (f : A → B → B) (e : B) (x y : List A)
             → foldr f e (x ++ y) ≡ foldr f (foldr f e y) x
foldr-++ f e [] y = refl
foldr-++ f e (a ∷ x) y rewrite foldr-++ f e x y = refl

postulate
    take#n : {A : Set} (x y : List A) → take (length x) (x ++ y) ≡ x
    drop#n : {A : Set} (x y : List A) → drop (length x) (x ++ y) ≡ y
    take#nk : ∀ {A : Set} k (x y : List A) 
              → take (length x + k) (x ++ y) ≡ x ++ take k y
    drop#nk : ∀ {A : Set} k (x y : List A) 
              → drop (length x + k) (x ++ y) ≡ drop k y
    takeNE : ∀ {A : Set} n {x : List A} 
             → NonEmpty x → zero < n → NonEmpty (take n x)
    dropNE : ∀ {A : Set} n {x : List A} 
             → NonEmpty x → n < length x → NonEmpty (drop n x)