module Prefix where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List
open import List+
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Utilities -- using (r-id-++-[])

import AlgebraicReasoning.PolyPreorderReasoning as PPR

open import AlgebraicReasoning.Equality

infixr 4 _⊑_ _⊏_
 
data _⊑_ {A : Set} : List A → List A → Set where
  [] : ∀ {x} → [] ⊑ x
  _∷_ : ∀ a {x y} → x ⊑ y → (a ∷ x) ⊑ (a ∷ y)

⊑-refl : ∀ {A} {x : List A} → x ⊑ x
⊑-refl {x = []} = []
⊑-refl {x = (a ∷ x)} = a ∷ ⊑-refl 

⊑-trans : ∀ {A} {x y z : List A} → x ⊑ y → y ⊑ z → x ⊑ z
⊑-trans [] _ = []
⊑-trans (a ∷ x⊑y) (.a ∷ y⊑z) = a ∷ ⊑-trans x⊑y y⊑z

module ⊑-reasoning = PPR.UnaryCarrier List _⊑_ ⊑-refl ⊑-trans
  renaming (begin_ to ⊑-begin_ ; _∼⟨_⟩_ to _⊑⟨_⟩_ ; _∎ to _⊑∎)

++-⊑ : ∀ {A : Set} (z : List A) {x y} → x ⊑ y → z ++ x ⊑ z ++ y
++-⊑ [] x⊑y = x⊑y
++-⊑ (a ∷ z) x⊑y = a ∷ ++-⊑ z x⊑y

⊑-++ : ∀ {A : Set} (x y : List A) → x ⊑ x ++ y
⊑-++ [] y = []
⊑-++ (a ∷ x) y = a ∷ ⊑-++ x y

¬++-⊑ : ∀ {A : Set} (x : List A) a y → ¬ (x ++ a ∷ y ⊑ x)
¬++-⊑ [] a y ()
¬++-⊑ (b ∷ x) a y (.b ∷ xay⊑x) = ¬++-⊑ x a y xay⊑x

⊑-≡ : ∀ {A : Set} {x y : List A} → x ⊑ y → y ⊑ x → x ≡ y
⊑-≡ [] [] = refl
⊑-≡ (a ∷ x⊑y) (.a ∷ y⊑x) rewrite ⊑-≡ x⊑y y⊑x = refl

_⊏_ : ∀ {A} → List A → List A → Set
x ⊏ y = x ⊑ y × ¬ (x ≡ y)    -- is it a good choice?

prefixes : ∀ {A} → List A → List⁺ (List A)
prefixes [] = [ [] ]⁺
prefixes (a ∷ x) = [] ∷ map⁺ (_∷_ a) (prefixes x)

∈-map∷ : ∀ {A} (a : A) {x : List A} {xs : List⁺ (List A)}
         → x ∈ xs → _∈_ {List A} (a ∷ x) (map⁺ (_∷_ a) xs)
∈-map∷ a (here₁ refl) = here₁ refl
∈-map∷ a (here₂ refl) = here₂ refl
∈-map∷ a (there x∈) = there (∈-map∷ a x∈)

∈-map∷-inv : ∀ {A a} {x : List A} {xs : List⁺ (List A)}
             → x ∈ map⁺ (_∷_ a) xs
             → ∃ (λ x' → x ≡ a ∷ x' × x' ∈ xs)
∈-map∷-inv {a = a} {.(a ∷ y)} {[ y ]⁺} (here₁ refl) = y , refl , here₁ refl
∈-map∷-inv {A} {a} {.(a ∷ y)} {y ∷ xs} (here₂ refl) = y , refl , here₂ refl
∈-map∷-inv {A} {a} {x} {y ∷ xs} (there x∈) with ∈-map∷-inv x∈
∈-map∷-inv {A} {a} {.(a ∷ x')} {y ∷ xs} (there x∈) | (x' , refl , x'∈) = 
  x' , refl , there x'∈

prefixes-⊑ : ∀ {A : Set} {x y : List A} → x ∈ prefixes y → x ⊑ y
prefixes-⊑ {y = []} (here₁ refl) = []
prefixes-⊑ {x = .[]} {a ∷ y} (here₂ refl) = []
prefixes-⊑ {y = a ∷ y} (there x∈) with ∈-map∷-inv x∈
prefixes-⊑ {x =.(a ∷ x')} {a ∷ y} (there x∈) | x' , refl , x'∈ = a ∷ prefixes-⊑ x'∈

⊑-prefixes : ∀ {A : Set} {x y : List A} → x ⊑ y → x ∈ prefixes y
⊑-prefixes {y = []} [] = here₁ refl
⊑-prefixes {y = _ ∷ _} [] = here₂ refl
⊑-prefixes (a ∷ x⊑y) = there (∈-map∷ a (⊑-prefixes x⊑y))

⊑-decompose : ∀ {A} {x y : List A} → x ⊑ y → ∃ (λ z → y ≡ x ++ z)
⊑-decompose {_} {.[]} {y} [] = y , refl
⊑-decompose {_} {.a ∷ x} (a ∷ x⊑y) with ⊑-decompose x⊑y
⊑-decompose {_} {.a ∷ x} {.(a ∷ x ++ z)} (a ∷ x⊑y) | (z , refl) = z , refl

⊏-decompose : ∀ {A} {x y : List A} → x ⊏ y → ∃ (λ a → ∃ (λ z → y ≡ x ++ a ∷ z))
⊏-decompose (x⊑y , x≠y) with ⊑-decompose x⊑y 
⊏-decompose {_} {x} (x⊑y , x≠y)| ([] , refl) rewrite r-id-++-[] x = ⊥-elim (x≠y refl)
⊏-decompose (x⊑y , x≠y)| (a ∷ z , refl) = a , z , refl

suffixes : {A : Set} → List A → List⁺ (List A)
suffixes [] = [ [] ]⁺
suffixes (a ∷ x) = (a ∷ x) ∷ suffixes x

id∈prefixes : ∀ {A} (x : List A) → x ∈ prefixes x
id∈prefixes [] = here₁ refl
id∈prefixes (a ∷ x) = there (∈-map∷ a (id∈prefixes x))

prefixes-decompose : ∀ {A : Set} (x : List A) a y 
  → prefixes (x ++ a ∷ y) ≡
    prefixes x ++⁺ map⁺ (_++_ (x ++ [ a ])) (prefixes y)
prefixes-decompose [] a y = refl
prefixes-decompose (b ∷ x) a y = 
  ≡-begin 
    prefixes (b ∷ x ++ a ∷ y)
  ≡⟨ refl ⟩ 
    [] ∷ map⁺ (_∷_ b) (prefixes (x ++ a ∷ y)) 
  ≡⟨ cong (λ e → [] ∷ map⁺ (_∷_ b) e ) (prefixes-decompose x a y) ⟩ 
    [] ∷ map⁺ (_∷_ b) (prefixes x ++⁺ map⁺ (_++_ (x ++ [ a ])) (prefixes y))
  ≡⟨ cong (_∷_ []) (map⁺-++⁺ (_∷_ b) (prefixes x) _) ⟩ 
    [] ∷ map⁺ (_∷_ b) (prefixes x) ++⁺
         map⁺ (_∷_ b) (map⁺ (_++_ (x ++ [ a ])) (prefixes y))
  ≡⟨ cong (λ e → [] ∷ map⁺ (_∷_ b) (prefixes x) ++⁺ e) 
     (map⁺-functor (_∷_ b) (_++_ (x ++ [ a ])) (prefixes y)) ⟩ 
   [] ∷ map⁺ (_∷_ b) (prefixes x) ++⁺
        map⁺ (λ e → b ∷ (x ++ [ a ]) ++ e) (prefixes y)
  ≡⟨ refl ⟩ 
   prefixes (b ∷ x) ++⁺
       map⁺ (λ e → b ∷ (x ++ [ a ]) ++ e) (prefixes y)
  ≡⟨ refl ⟩ 
   prefixes (b ∷ x) ++⁺
      map⁺ (λ e → (b ∷ x ++ [ a ]) ++ e) (prefixes y)
  ≡∎

++-prefixes→ : ∀ {A : Set} (u : List A) {x y} 
               → x ∈ prefixes y → u ++ x ∈ prefixes (u ++ y)
++-prefixes→ u x∈ = ⊑-prefixes (++-⊑ u (prefixes-⊑ x∈))

++-prefixes← : ∀ {A : Set} (u : List A) {x y} 
               → u ++ x ∈ prefixes (u ++ y) → x ∈ prefixes y
++-prefixes← [] ux∈ = ux∈
++-prefixes← (a ∷ u) (here₂ ())
++-prefixes← (a ∷ u) (there aux∈) with ∈-map∷-inv aux∈
++-prefixes← (a ∷ u) {x} (there aux∈)| (.(u ++ x) , refl , ux∈) = ++-prefixes← u ux∈

prefix-⊐-⊑ : ∀ {A : Set} {x y z : List A} → x ⊑ z → y ⊑ z → ¬ (y ⊏ x) → x ⊑ y
prefix-⊐-⊑ {A} {.[]} {.[]} {[]} [] [] _ = []
prefix-⊐-⊑ {A} {.[]} {y} {a ∷ z} [] y⊑ neg = []
prefix-⊐-⊑ {A} {.a ∷ x} {.[]} {a ∷ z} (.a ∷ y) [] neg = 
    ⊥-elim (neg ([] , λ ()))
prefix-⊐-⊑ {A} {.a ∷ x} {.a ∷ y} {a ∷ z} (.a ∷ x⊑) (.a ∷ y⊑) neg = 
    a ∷ prefix-⊐-⊑ x⊑ y⊑ neg'
  where ∷-inv : ∀ {A : Set} (a : A) {x y : List A} → _≡_ {_}{List A} (a ∷ x) (a ∷ y) → x ≡ y
        ∷-inv a refl = refl
        neg' : ¬ (y ⊏ x)
        neg' (y⊑x , y≠x) = neg (a ∷ y⊑x , (λ eq → y≠x (∷-inv a eq)))

prefixes-snoc : ∀ {A} → (xs : List A) → SnocWF xs → List⁺ (List A)
prefixes-snoc .[] [] = [ [] ]⁺
prefixes-snoc .(x ++ a ∷ []) (∷ʳ-wf x wf a) = prefixes-snoc x wf ++⁺ [ x ∷ʳ a ]⁺

prefixes-∷ʳ : ∀ {A} (x : List A) a 
              → prefixes (x ∷ʳ a) ≡ prefixes x ++⁺ [ x ∷ʳ a ]⁺
prefixes-∷ʳ [] a = refl
prefixes-∷ʳ {A} (b ∷ x) a 
  rewrite prefixes-∷ʳ x a 
        | map⁺-++⁺ {List A}{List A} (_∷_ b) (prefixes x) [ x ++ a ∷ [] ]⁺
  = refl

-- prefixes for partitions

prefixes-parts : ∀ {A} → (xs : List (List A)) → List⁺ (List A)
prefixes-parts [] = [ [] ]⁺
prefixes-parts (x ∷ xs) = 
   init⁺ (prefixes x) ++⁺' map⁺ (_++_ x) (prefixes-parts xs)
