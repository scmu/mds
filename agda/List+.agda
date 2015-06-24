module List+ where

open import Data.Product
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Data.List

infixr 5 _∷_ _++⁺_

data List⁺ (A : Set) : Set where
  [_]⁺ : (a : A) → List⁺ A
  _∷_ : (a : A) → (x : List⁺ A) → List⁺ A

foldr⁺ : ∀ {A B : Set} → (A → B → B) → (A → B) → List⁺ A → B
foldr⁺ f g [ a ]⁺ = g a
foldr⁺ f g (a ∷ x) = f a (foldr⁺ f g x)

map⁺ : ∀ {A B} → (A → B) → List⁺ A → List⁺ B
-- map⁺ f = foldr⁺ (λ a x → f a ∷ x) (λ x → [ f x ]⁺)
map⁺ f [ a ]⁺ = [ f a ]⁺
map⁺ f (a ∷ x) = f a ∷ map⁺ f x

map⁺-id : ∀ {A} (f : A → A) → (∀ a → f a ≡ a) 
          → ∀ x → map⁺ f x ≡ x
map⁺-id f fid [ a ]⁺ rewrite fid a = refl
map⁺-id f fid (a ∷ x) rewrite fid a | map⁺-id f fid x = refl

map⁺-functor : ∀ {A B C} (f : B → C) (g : A → B)
               → (x : List⁺ A)
               → map⁺ f (map⁺ g x) ≡ map⁺ (f ∘ g) x
map⁺-functor f g [ a ]⁺ = refl
map⁺-functor f g (a ∷ x) rewrite map⁺-functor f g x = refl

map⁺-cong : ∀ {A B} (f g : A → B)
            → (∀ a → f a ≡ g a)
            → (x : List⁺ A)
            → map⁺ f x ≡ map⁺ g x
map⁺-cong f g eq [ a ]⁺ rewrite eq a = refl
map⁺-cong f g eq (a ∷ x) rewrite eq a | map⁺-cong f g eq x = refl

_++⁺_ : ∀ {A} → List⁺ A → List⁺ A → List⁺ A
[ a ]⁺ ++⁺ y = a ∷ y
(a ∷ x) ++⁺ y = a ∷ (x ++⁺ y)

_++⁺'_ : ∀ {A} → List A → List⁺ A → List⁺ A
[] ++⁺' y = y
(a ∷ x) ++⁺' y = a ∷ (x ++⁺' y)

head⁺ : ∀ {A} → List⁺ A → A
head⁺ [ a ]⁺ = a
head⁺ (a ∷ x) = a

init⁺ : ∀ {A} → List⁺ A → List A 
init⁺ [ a ]⁺ = []
init⁺ (a ∷ x) = a ∷ init⁺ x

last⁺ : ∀ {A} → List⁺ A → A
last⁺ [ a ]⁺ = a
last⁺ (_ ∷ x) = last⁺ x

last⁺-++⁺ : ∀ {A} (x : List⁺ A) a → last⁺ (x ++⁺ [ a ]⁺) ≡ a
last⁺-++⁺ [ b ]⁺ a = refl
last⁺-++⁺ (b ∷ x) a = last⁺-++⁺ x a

head⁺-natural : ∀ {A B} (f : A → B) (x : List⁺ A)
                → head⁺ (map⁺ f x) ≡ f (head⁺ x)
head⁺-natural f [ a ]⁺ = refl
head⁺-natural f (a ∷ x) = refl

map⁺-++⁺ : ∀ {A B} (f : A → B) (x y : List⁺ A)
          → map⁺ f (x ++⁺ y) ≡ map⁺ f x ++⁺ map⁺ f y
map⁺-++⁺ f [ a ]⁺ y = refl
map⁺-++⁺ f (a ∷ x) y rewrite map⁺-++⁺ f x y = refl

scanr⁺ : ∀ {A B : Set} → (A → B → B) → B → List A → List⁺ B
scanr⁺ f e = foldr (λ a y → f a (head⁺ y) ∷ y) [ e ]⁺

scanr⁺-head-foldr : ∀ {A B} → (f : A → B → B) → (e : B) 
                    → head⁺ ∘ scanr⁺ f e ≗ foldr f e
scanr⁺-head-foldr {A} {B} f e = 
  foldr-fusion head⁺ [ e ]⁺ fcond
 where 
  open import Data.List.Properties using (foldr-fusion) 
  fcond : ∀ a y → head⁺ (f a (head⁺ y) ∷ y) ≡ f a (head⁺ y)
  fcond a y = refl

map⁺-scanr⁺-fusion : 
  ∀ {A B C : Set} 
    (h : B → C) {f : A → B → B} {g : A → C → C} (e : B) →
    (∀ x y → h (f x y) ≡ g x (h y)) →
    map⁺ h ∘ scanr⁺ f e ≗ scanr⁺ g (h e)
map⁺-scanr⁺-fusion {A} {B} h {f} {g} e fcond = 
    foldr-fusion (map⁺ h) [ e ]⁺ fcond'
 where 
    open import Data.List.Properties using (foldr-fusion) 
    open import AlgebraicReasoning.Equality

    fcond' : ∀ a y → map⁺ h (f a (head⁺ y) ∷ y) ≡ 
                     g a (head⁺ (map⁺ h y)) ∷ map⁺ h y
    fcond' a y = 
      ≡-begin 
        map⁺ h (f a (head⁺ y) ∷ y) 
      ≡⟨ refl ⟩
        h (f a (head⁺ y)) ∷ map⁺ h y 
      ≡⟨ cong (λ e → e ∷ map⁺ h y) (fcond a (head⁺ y)) ⟩ 
        g a (h (head⁺ y)) ∷ map⁺ h y 
      ≡⟨ cong (λ e → g a e ∷ map⁺ h y) (sym (head⁺-natural h y)) ⟩ 
        g a (head⁺ (map⁺ h y)) ∷ map⁺ h y 
      ≡∎

foldr-fusion-Inv : 
  ∀ {A B C : Set} (h : B → C) {f : A → B → B} {g : A → C → C} (e : B) 
  → (Inv : C → Set)
  → (∀ a b → Inv (h b) → h (f a b) ≡ g a (h b)) 
  → (∀ x → Inv (foldr g (h e) x))
  → h ∘ foldr f e ≗ foldr g (h e)
foldr-fusion-Inv h e Inv fcond inv [] = refl
foldr-fusion-Inv h {f} {g} e Inv fcond inv (a ∷ x) = 
  ≡-begin 
    h (foldr f e (a ∷ x)) 
  ≡⟨ refl ⟩ 
    h (f a (foldr f e x)) 
  ≡⟨ fcond a (foldr f e x) 
    (subst Inv (sym (foldr-fusion-Inv h e Inv fcond inv x)) (inv x)) ⟩ 
    g a (h (foldr f e x)) 
  ≡⟨ cong (g a) (foldr-fusion-Inv h e Inv fcond inv x) ⟩ 
    g a (foldr g (h e) x) 
  ≡⟨ refl ⟩ 
    foldr g (h e) (a ∷ x) 
  ≡∎
 where open import AlgebraicReasoning.Equality

data All⁺ {A : Set} (P : A → Set) : List⁺ A → Set where
  [_]⁺ : ∀ {a} → P a → All⁺ P [ a ]⁺
  _∷_ : ∀ {a x} → P a → All⁺ P x → All⁺ P (a ∷ x)

All⁺-head⁺ : ∀ {A B} (P : B → Set) (f : A → B) →
            ∀ x →  All⁺ P (map⁺ f x) → P (f (head⁺ x))
All⁺-head⁺ P f [ a ]⁺ [ p ]⁺ = p
All⁺-head⁺ P f (a ∷ x) (p ∷ _) = p

All⁺-foldr-scanr⁺ : 
    ∀ {A B : Set} (P : B → Set) (f : A → B → B) (e : B)
    → (∀ x → P (foldr f e x))
    → ∀ x → All⁺ P (scanr⁺ f e x)
All⁺-foldr-scanr⁺ P f e inv [] = [ inv [] ]⁺
All⁺-foldr-scanr⁺ P f e inv (a ∷ x) 
    rewrite scanr⁺-head-foldr f e x = 
  inv (a ∷ x) ∷ All⁺-foldr-scanr⁺ P f e inv x

map⁺-scanr⁺-fusion-Inv : 
  ∀ {A B C : Set} 
    (h : B → C) {f : A → B → B} {g : A → C → C} (e : B)
  → (Inv : C → Set)
  → (∀ a b → Inv (h b) → h (f a b) ≡ g a (h b))
  → (∀ x → Inv (foldr g (h e) x))
  →  map⁺ h ∘ scanr⁺ f e ≗ scanr⁺ g (h e)
map⁺-scanr⁺-fusion-Inv {A} {B} h {f} {g} e Inv fcond inv = 
    foldr-fusion-Inv (map⁺ h) [ e ]⁺ (All⁺ Inv) fcond'
       (All⁺-foldr-scanr⁺ Inv g (h e) inv)
 where 
    open import Data.List.Properties using (foldr-fusion) 
    open import AlgebraicReasoning.Equality

    fcond' : ∀ a y 
             → All⁺ Inv (map⁺ h y)
             → map⁺ h (f a (head⁺ y) ∷ y) ≡ 
               g a (head⁺ (map⁺ h y)) ∷ map⁺ h y
    fcond' a y inv* =
      ≡-begin 
        map⁺ h (f a (head⁺ y) ∷ y) 
      ≡⟨ refl ⟩
        h (f a (head⁺ y)) ∷ map⁺ h y 
      ≡⟨ cong (λ e → e ∷ map⁺ h y) 
         (fcond a (head⁺ y) (All⁺-head⁺ Inv h y inv*)) ⟩ 
        g a (h (head⁺ y)) ∷ map⁺ h y 
      ≡⟨ cong (λ e → g a e ∷ map⁺ h y) (sym (head⁺-natural h y)) ⟩ 
        g a (head⁺ (map⁺ h y)) ∷ map⁺ h y 
      ≡∎

infixr 4 _∈_

data Any⁺ {A : Set} (P : A → Set) : List⁺ A → Set where
  here₁ : ∀ {a} → P a → Any⁺ P [ a ]⁺
  here₂ : ∀ {a x} → P a → Any⁺ P (a ∷ x)
  there : ∀ {a x} → Any⁺ P x → Any⁺ P (a ∷ x)

_∈_ : {A : Set} → A → List⁺ A → Set
a ∈ x = Any⁺ (_≡_ a) x

∈-pred : ∀ {A : Set} {a : A} {x} {P : A → Set}
         → P a → a ∈ x → Any⁺ P x
∈-pred p (here₁ refl) = here₁ p
∈-pred p (here₂ refl) = here₂ p
∈-pred p (there a∈) = there (∈-pred p a∈)

map⁺-pred : ∀ {A B} (f : A → B) (P : B → Set)
           → (∀ a → P (f a)) → ∀ x
           → ∀ {b} → b ∈ map⁺ f x → P b
map⁺-pred f P pf [ a ]⁺ (here₁ refl) = pf a
map⁺-pred f P pf (a ∷ x) (here₂ refl) = pf a
map⁺-pred f P pf (a ∷ x) (there b∈) = map⁺-pred f P pf x b∈

map⁺-pred→ : ∀ {A B} (f : A → B) (P : B → Set) →
             ∀ {b x} → b ∈ map⁺ f x → P b →
             ∃ (λ a → a ∈ x × P (f a))
map⁺-pred→ f P {.(f a)} {[ a ]⁺} (here₁ refl) Pb = a , here₁ refl , Pb
map⁺-pred→ f P {.(f a)} {a ∷ x} (here₂ refl) Pb = a , here₂ refl , Pb
map⁺-pred→ f P {b} {a ∷ x} (there b∈) Pb 
  with map⁺-pred→ f P b∈ Pb
... | c , c∈ , Pfc = c , there c∈ , Pfc

map⁺-∈ : ∀ {A B} (f : A → B) {a x}
         → a ∈ x → f a ∈ map⁺ f x
map⁺-∈ f (here₁ refl) = here₁ refl
map⁺-∈ f (here₂ refl) = here₂ refl
map⁺-∈ f (there a∈) = there (map⁺-∈ f a∈)

import Data.List

List⁺-to-List : ∀ {A : Set} (xs : List⁺ A) → List A
List⁺-to-List [ a ]⁺ = a ∷ []
List⁺-to-List (a ∷ x) = a ∷ List⁺-to-List x 

data Adj⁺ {A} (R : A → A → Set) : List⁺ A → Set where
  [·] : ∀ {a} → Adj⁺ R [ a ]⁺
  _∷[·] : ∀ {a b} → R a b → Adj⁺ R (a ∷ [ b ]⁺)
  _∷_ : ∀ {a b x} → R a b → Adj⁺ R (b ∷ x) → Adj⁺ R (a ∷ b ∷ x)

Adj⁺-snoc : ∀ {A} {R : A → A → Set} x a b 
            → Adj⁺ R (x ++⁺ [ a ]⁺) 
            → R a b 
            → Adj⁺ R ((x ++⁺ [ a ]⁺) ++⁺ [ b ]⁺)
Adj⁺-snoc [ c ]⁺ a b (cRa ∷[·]) aRb = cRa ∷ aRb ∷[·]
Adj⁺-snoc (c ∷ [ d ]⁺) a b (cRd ∷ dRa ∷[·]) aRb = cRd ∷ dRa ∷ aRb ∷[·]
Adj⁺-snoc (c ∷ d ∷ x) a b (cRd ∷ dxa) aRb = cRd ∷ Adj⁺-snoc (d ∷ x) a b dxa aRb

Adj⁺-trans : ∀ {A} {R : A → A → Set} 
             → (∀ {x y z} → R x y → R y z → R x z) →
             ∀ a x → Adj⁺ R (a ∷ x) → R a (last⁺ x)
Adj⁺-trans trans a .([ b ]⁺) (_∷[·] {.a} {b} aRb) = aRb
Adj⁺-trans trans a .(b ∷ x) (_∷_ {.a} {b} {x} aRb adj) 
  with Adj⁺-trans trans b x adj 
... | bRz = trans aRb bRz

-- a … b ∈ x -- a occurs before b in x.

data _…_∈_ {A : Set} : A → A → List⁺ A → Set where
  here : ∀ {a b x} → b ∈ x → a … b ∈ x
  there : ∀ {c a b x} → a … b ∈ x → a … b ∈ (c ∷ x)
