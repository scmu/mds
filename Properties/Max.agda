module Properties.Max where

open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.Sum
open import Function using (_∘_; id)
open import Data.Nat
open import Data.List

open import Relation.Nullary
open import Relation.Binary

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Elem
open import List+
open import Prefix
open import MDS
open import Utilities

open import AlgebraicReasoning.Implications 
open import AlgebraicReasoning.Equality

max-∈ : ∀ {A _⊔_} → Choose _⊔_ → (x : List⁺ A) → max-with _⊔_ x ∈ x
max-∈ _ [ a ]⁺ = here₁ refl
max-∈ {A} {_⊔_} choose (a ∷ x) with choose a (max-with _⊔_ x)
max-∈ choose (a ∷ x) | inj₁ eq rewrite eq = here₂ refl
max-∈ choose (a ∷ x) | inj₂ eq rewrite eq = there (max-∈ choose x)

max-pred : ∀ {A _⊔_} → Choose _⊔_ 
           → (P : A → Set) (x : List⁺ A)
           → (∀ {a} → a ∈ x → P a) → P (max-with _⊔_ x)
max-pred choose P x all = all (max-∈ choose x)

max≼-∈ : ∀ xs → max≼ xs ∈ xs
max≼-∈ = max-∈ Choose-↑≼

max≼-pred : (P : List Elem → Set) (xs : List⁺ (List Elem))
          → (∀ {x} → x ∈ xs → P x) → P (max≼ xs)
max≼-pred = max-pred Choose-↑≼

maxd-∈ : ∀ xs → maxd xs ∈ xs
maxd-∈ = max-∈ Choose-↑d

maxd-pred : (P : List Elem → Set) (xs : List⁺ (List Elem))
          → (∀ {x} → x ∈ xs → P x) → P (maxd xs)
maxd-pred = max-pred Choose-↑d

max≼-we : ∀ {xs} → Any⁺ we xs → we (max≼ xs)
max≼-we (here₁ we) = we
max≼-we (here₂ we) = ↑≼-we₁ we
max≼-we (there we) = ↑≼-we₂ (max≼-we we)

max≼-++ : ∀ x y → max≼ (x ++⁺ y) ≡ max≼ x ↑≼ max≼ y
max≼-++ [ a ]⁺ y = refl
max≼-++ (a ∷ x) y = 
  ≡-begin 
    max≼ (a ∷ x ++⁺ y) 
  ≡⟨ refl ⟩ 
    a ↑≼ max≼ (x ++⁺ y)
  ≡⟨ cong (_↑≼_ a) (max≼-++ x y) ⟩ 
    a ↑≼ (max≼ x ↑≼ max≼ y)
  ≡⟨ ↑≼-assoc ⟩ 
    (a ↑≼ max≼ x) ↑≼ max≼ y 
  ≡⟨ refl ⟩ 
    max≼ (a ∷ x) ↑≼ max≼ y 
  ≡∎

max≼-pred→ : (P : List Elem → Set) → 
  ∀ xs → P (max≼ xs) → ∃ (λ x → x ∈ xs × P x)
max≼-pred→ P [ a ]⁺ Pm = a , here₁ refl , Pm
max≼-pred→ P (a ∷ x) Pm with ↑≼-either a (max≼ x) 
... | inj₁ eq rewrite eq = a , here₂ refl , Pm
... | inj₂ eq rewrite eq with max≼-pred→ P x Pm
...   | b , b∈ , Pb = b , there b∈ , Pb

max≼-maximum : ∀ {x} ys → x ∈ ys → x ≼ max≼ ys
max≼-maximum .([ y ]⁺) (here₁ {y} refl) = ≼-refl
max≼-maximum .(y ∷ ys) (here₂ {y} {ys} refl) = ↑≼-max-l _ _
max≼-maximum .(y ∷ ys) (there {y} {ys} x∈) with ↑≼-either' y (max≼ ys)
... | inj₁ (eq , mys≼y) rewrite eq = ≼-trans (max≼-maximum ys x∈) mys≼y
... | inj₂ (eq , _ , _) rewrite eq = max≼-maximum ys x∈

postulate
  maxd-maximum : ∀ {x} ys → x ∈ ys → x ≤d maxd ys

max-prefix-++ : ∀ {A B} → (f : List A → B) → {_⊔_ : B → B → B}
                → Idem _⊔_ → Assoc _⊔_
                → (x y : List A)
                → max-with _⊔_ (map⁺ f (prefixes (x ++ y)))
                  ≡ max-with _⊔_ (map⁺ f (prefixes x)) ⊔
                    max-with _⊔_ (map⁺ (f ∘ (_++_ x)) (prefixes y))
max-prefix-++ f idem _ [] [] rewrite idem (f []) = refl
max-prefix-++ f {_⊔_} idem assoc [] (b ∷ y) 
  rewrite assoc (f []) (f []) (max-with _⊔_ (map⁺ f (map⁺ (_∷_ b) (prefixes y)))) 
        | idem (f []) = refl
max-prefix-++ f {_⊔_} idem assoc (a ∷ x) y 
  rewrite sym (assoc (f []) (max-with _⊔_ (map⁺ f (map⁺ (_∷_ a) (prefixes x))))
                     (max-with _⊔_ (map⁺ (λ x' → f (a ∷ x ++ x')) (prefixes y))))
        | map⁺-functor f (_∷_ a) (prefixes (x ++ y))
        | map⁺-functor f (_∷_ a) (prefixes x)
        | max-prefix-++ (f ∘ (_∷_ a)) {_⊔_} idem assoc x y 
   = refl

maxd-prefix-++ : ∀ {A} → (f : List A → List Elem)
                → (x y : List A)
                → maxd (map⁺ f (prefixes (x ++ y)))
                  ≡ maxd (map⁺ f (prefixes x)) ↑d
                    maxd (map⁺ (f ∘ (_++_ x)) (prefixes y))
maxd-prefix-++ f x y = max-prefix-++ f ↑d-idem ↑d-assoc x y

max-snoc : ∀ {A} {_⊔_ : A → A → A}
           → Assoc _⊔_ →
           ∀ x a → max-with _⊔_ (x ++⁺ [ a ]⁺) ≡ (max-with _⊔_ x) ⊔ a
max-snoc assoc [ b ]⁺ a = refl
max-snoc {A} {_⊔_} assoc (b ∷ x) a 
  rewrite max-snoc {A} {_⊔_} assoc x a 
        = assoc b (max-with _⊔_ x) a

maxd-snoc : ∀ x a → maxd (x ++⁺ [ a ]⁺) ≡ (maxd x) ↑d a
maxd-snoc x a = max-snoc ↑d-assoc x a

max-snoc2 : ∀ {A} {_⊔_ : A → A → A}
            → Assoc _⊔_ →
            ∀ x a b → max-with _⊔_ ((x ++⁺ [ a ]⁺) ++⁺ [ b ]⁺) 
                      ≡ (max-with _⊔_ x) ⊔ (a ⊔ b)
max-snoc2 {A} {_⊔_} assoc x a b 
  rewrite max-snoc {A} {_⊔_} assoc (x ++⁺ [ a ]⁺) b
        | max-snoc {A} {_⊔_} assoc x a 
        = sym (assoc (max-with _⊔_ x) a b)

maxd-snoc2 : ∀ x a b → maxd ((x ++⁺ [ a ]⁺) ++⁺ [ b ]⁺) 
                       ≡ (maxd x) ↑d (a ↑d b)
maxd-snoc2 = max-snoc2 ↑d-assoc

maxd-increasing : ∀ {xs} → Adj⁺ _<d_ xs → maxd xs ≡ last⁺ xs
maxd-increasing [·] = refl
maxd-increasing (a<b ∷[·]) = ↑d-right a<b
maxd-increasing (a<b ∷ inc) rewrite maxd-increasing inc = 
   ↑d-right (Adj⁺-trans <d-trans _ _ (a<b ∷ inc))

{-
max-natural : ∀ {A B} {_⊔_ : B → B → B} 
              → (f : A → B)
              → ∀ (x : List⁺ A)
              → max-with {B} _⊔_ (map⁺ f x) ≡ 
                f (max-with {A} (λ a b → (f a) ⊔ (f b)) x)
max-natural {A} {B} _⊔_ f x = ? -}

max-with-left : ∀ {A} {↑ : A → A → A} {≼ : A → A → Set}
            → Choose-Left ↑ ≼ → List⁺ A → List A
max-with-left choose [ x ]⁺ = []
max-with-left {A} {↑} choose (x ∷ xs) with choose x (max-with ↑ xs) 
... | inj₁ _ = []
... | inj₂ _ = x ∷ max-with-left choose xs

predecessors : ∀ {A} {a} {x : List⁺ A} → a ∈ x → List A
predecessors (here₁ _) = []
predecessors (here₂ _) = []
predecessors (there {b} {x} a∈) = b ∷ predecessors a∈

open import Data.List.Any using (Any; here; there)
open Data.List.Any.Membership-≡ renaming (_∈_ to _∈⁻_)

max-left-≺ : ∀ {A} {↑ : A → A → A} {_≼_ : A → A → Set}
             → (choose : Choose-Left ↑ _≼_)
             → ∀ {a} {x}
             → a ∈⁻ max-with-left choose x
             → let _≺_ : A → A → Set
                   x ≺ y = x ≼ y × ¬ (y ≼ x) 
               in a ≺ max-with ↑ x
max-left-≺ ch {a} {[ _ ]⁺} ()
max-left-≺ {_} {_↑_} ch {a} {b ∷ x} a∈ with ch b (max-with _↑_ x) 
max-left-≺ {_} {_↑_} ch {a} {b ∷ x} () | inj₁ _ 
max-left-≺ {_} {_↑_} ch {a} {b ∷ x} (here a≡b) | inj₂ (eq , b≺mx) rewrite eq | a≡b = b≺mx
max-left-≺ {_} {_↑_} ch {a} {b ∷ x} (there a∈) | inj₂ (eq , b≺mx) rewrite eq = 
  max-left-≺ ch {a} {x} a∈

{- Not correct.

max-predeces-≺ : ∀ {A} {↑ : A → A → A} {_≼_ : A → A → Set}
                 → (Choose-Left ↑ _≼_)
                 → ∀ {a} {x}
                 → (max∈ : max-with ↑ x ∈ x)
                 → a ∈⁻ predecessors max∈ 
                 → let _≺_ : A → A → Set
                       x ≺ y = x ≼ y × ¬ (y ≼ x) 
                   in a ≺ max-with ↑ x
max-predeces-≺ ch {a} {[ _ ]⁺} (here₁ _) ()
max-predeces-≺ ch {a} {b ∷ x} (here₂ _) ()
max-predeces-≺ {A} {_↑_} ch {a} {b ∷ x} (there max∈) a∈ with ch b (max-with _↑_ x)
max-predeces-≺ {A} {_↑_} ch {a} {b ∷ x} (there max∈) a∈ | inj₁ (eq , mx≼b) 
    rewrite eq = {!!}
max-predeces-≺ {A} {_↑_} ch {a} {b ∷ x} (there max∈) a∈ | inj₂ (eq , _) rewrite eq = max-predeces-≺ ch {a} {x} max∈ {!!}
-}

open import Prefix

private

  pre-pre : ∀ {A} {↑ : List A → List A → List A} {≼ : List A → List A → Set}
            → (choose : Choose-Left ↑ ≼)
            → ∀ z y x 
            → z ++ y ⊏ max-with ↑ (map⁺ (_++_ z) (prefixes x))
            → z ++ y ∈⁻ max-with-left choose (map⁺ (_++_ z) (prefixes x))
  pre-pre ch z [] [] (_ , ¬refl) = ⊥-elim (¬refl refl)
  pre-pre ch z (b ∷ y) [] (zby⊑z , _) rewrite r-id-++-[] z = ⊥-elim (¬++-⊑ z b y zby⊑z)
  pre-pre {_} {↑} ch z y (a ∷ x) y∈  
    rewrite r-id-++-[] z 
          | map⁺-functor (_++_ z) (_∷_ a) (prefixes x) 
    with ch z (max-with ↑ (map⁺ (λ w → z ++ a ∷ w) (prefixes x))) 
  pre-pre ch z []      (a ∷ x) (_ , ¬refl) | inj₁ (eq , _) 
    rewrite eq | r-id-++-[] z = ⊥-elim (¬refl refl)
  pre-pre ch z (b ∷ y) (a ∷ x) (zby⊑z , _) | inj₁ (eq , _)
    rewrite eq = ⊥-elim (¬++-⊑ z b y zby⊑z)
  pre-pre ch z [] (a ∷ x) y∈ | inj₂ (eq , _) rewrite eq | r-id-++-[] z = here refl
  pre-pre {_} {↑} ch z (b ∷ y) (a ∷ x) y∈ | inj₂ (eq , _) 
    rewrite eq = there mem
   where mx⊑zaw : ∃ (λ w → (max-with ↑ (map⁺ (λ x' → z ++ a ∷ x') (prefixes x))) 
                          ≡ (z ++ a ∷ w))
         mx⊑zaw = max-pred (Choose-Left⇒Choose ch) 
                   P (map⁺ (λ w → z ++ a ∷ w) (prefixes x)) 
                   (map⁺-pred (λ w → z ++ a ∷ w) P (λ w → w , refl) (prefixes x))
           where P : List _ → Set
                 P x = ∃ (λ w → x ≡ z ++ a ∷ w)

         prefix-eq : ∀ z {b y a w} → z ++ b ∷ y ⊑ z ++ a ∷ w → b ≡ a
         prefix-eq [] (a ∷ _) = refl
         prefix-eq (_ ∷ z) (._ ∷ pre) = prefix-eq z pre

         b≡a : b ≡ a
         b≡a with y∈ | mx⊑zaw 
         ... | (zby⊑ , _) | (_ , eq) rewrite eq = prefix-eq z zby⊑

         mem : z ++ b ∷ y ∈⁻ max-with-left ch (map⁺ (λ w → z ++ a ∷ w) (prefixes x))
         mem with y∈
         mem | y∈ rewrite b≡a | assoc z [ a ] y 
                        | map⁺-cong (λ w → z ++ a ∷ w) (λ w → (z ++ [ a ]) ++ w) 
                           (λ w → assoc z [ a ] w) (prefixes x) 
           = pre-pre ch (z ++ [ a ]) y x y∈

pre-prefix : ∀ {A} {↑ : List A → List A → List A} {≼ : List A → List A → Set}
             → (choose : Choose-Left ↑ ≼)
             → ∀ y x 
             → y ⊏ max-with ↑ (prefixes x)
             → y ∈⁻ max-with-left choose (prefixes x)
pre-prefix {_} {↑} ch y x y⊏ with map⁺-id (λ w → [] ++ w) (λ _ → refl) (prefixes x)
... | eq = subst (λ xs → y ∈⁻ max-with-left ch xs) eq mem
   where mem : y ∈⁻ max-with-left ch (map⁺ (λ w → [] ++ w) (prefixes x))
         mem = pre-pre ch [] y x (subst (λ xs → y ⊏ max-with ↑ xs) (sym eq) y⊏)


prefix-≺ :  ∀ {A} {↑ : List A → List A → List A} {_≼_ : List A → List A → Set}
             → (choose : Choose-Left ↑ _≼_)
             → ∀ y x 
             → y ⊏ max-with ↑ (prefixes x)
             → let _≺_ : List A → List A → Set
                   x ≺ y = (x ≼ y) × (¬ (y ≼ x))
               in y ≺ max-with ↑ (prefixes x)
prefix-≺ ch y x y⊏ = max-left-≺ ch {y} {prefixes x} (pre-prefix ch y x y⊏)


-- d, dc, dcz, etz

max-d-dz : ∀ z xs → 
             maxd (map⁺ (_++_ z) xs) ≡ z ++ max-with (↑dz z) xs
max-d-dz z [ x ]⁺ = refl
max-d-dz z (x ∷ xs) rewrite max-d-dz z xs with (z ++ max-with (↑dz z) xs) ≤d? (z ++ x)
... | no _ = refl
... | yes _ = refl


max-d-dzc : ∀ z xss → 
              maxd (map⁺ ((_++_ z) ∘ concat) xss)
              ≡ z ++ concat (max-with (↑dzc z) xss)
max-d-dzc z [ xs ]⁺ = refl
max-d-dzc z (xs ∷ xss) rewrite max-d-dzc z xss 
  with (z ++ concat (max-with (↑dzc z) xss)) ≤d?
        (z ++ concat xs)
... | no _ = refl
... | yes _ = refl
