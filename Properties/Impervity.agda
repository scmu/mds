module Properties.Impervity where

open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.Sum
open import Function using (_∘_; id)
open import Data.Nat
open import Data.List

open import Relation.Nullary
open import Relation.Binary

open import Relation.Binary.PropositionalEquality

open import Elem
open import List+
open import Prefix
open import MDS
open import Utilities

open import Properties.Max

open import AlgebraicReasoning.Implications 
open import AlgebraicReasoning.Equality


{- 
  impervity lemma
    ∀ {x} → width x ≤ L → x ≡ wp x ≡ mdp x ≡ mds x
-}

impervity-id≡mdp-wf : ∀ {x} → SnocWF x → ¬ (we x) → x ≡ mdp x
impervity-id≡mdp-wf {.[]} [] □x = refl
impervity-id≡mdp-wf {.(x ++ a ∷ [])} (∷ʳ-wf x wf a) □xa
    rewrite prefixes-∷ʳ x a = fin
  where der : max≼ (prefixes x ++⁺ [ x ∷ʳ a ]⁺) 
              ≡ x ↑≼ (x ∷ʳ a)
        der = ≡-begin
                max≼ (prefixes x ++⁺ [ x ∷ʳ a ]⁺)
              ≡⟨ max≼-++ (prefixes x) [ x ∷ʳ a ]⁺ ⟩ 
                max≼ (prefixes x) ↑≼ (x ∷ʳ a)
              ≡⟨ cong (λ e → e ↑≼ (x ∷ʳ a)) 
                  (sym (impervity-id≡mdp-wf {x} wf (¬we-snoc □xa))) ⟩ 
                x ↑≼ (x ∷ʳ a)
              ≡∎
        fin : x ∷ʳ a ≡ max≼ (prefixes x ++⁺ [ x ∷ʳ a ]⁺) 
        fin rewrite der with we? x
        ... | yes ⊠x = ⊥-elim (¬we-snoc □xa ⊠x)
        ... | no _ with we? (x ++ a ∷ [])
        ...   | yes ⊠xa = ⊥-elim (□xa ⊠xa)
        ...   | no _ with width (x ++ a ∷ []) ≤? width x
        ...      | yes xa≤wx = ⊥-elim (width-snoc x a xa≤wx)
        ...      | no _ = refl

impervity-id≡mdp : ∀ {x} → ¬ (we x) → x ≡ mdp x
impervity-id≡mdp {x} □x = impervity-id≡mdp-wf (snocWF x) □x

impervity-id≡wp : ∀ {x} → ¬ (we x) → x ≡ wp x
impervity-id≡wp {[]} _ = refl
impervity-id≡wp {a ∷ x} □ax = sym der
  where der : wp (a ∷ x) ≡ a ∷ x
        der = ≡-begin 
                wp (a ∷ x) 
              ≡⟨ refl ⟩ 
                mdp (a ∷ wp x)
              ≡⟨ cong (λ e → mdp (a ∷ e)) (sym (impervity-id≡wp (¬we-∷ □ax))) ⟩ 
                mdp (a ∷ x)
              ≡⟨ sym (impervity-id≡mdp □ax) ⟩ 
                a ∷ x 
              ≡∎

impervity-id≡mds : ∀ {x} → ¬ (we x) → x ≡ mds x
impervity-id≡mds {[]} _ = refl
impervity-id≡mds {a ∷ x} □ax = sym (
   ≡-begin
     mds (a ∷ x) 
   ≡⟨ refl ⟩ 
     mdp (a ∷ x) ↑≼ mds x
   ≡⟨ cong (λ e → mdp (a ∷ x) ↑≼ e) (sym (impervity-id≡mds (¬we-∷ □ax))) ⟩ 
     mdp (a ∷ x) ↑≼ x 
   ≡⟨ cong (λ e → e ↑≼ x) (sym (impervity-id≡mdp □ax)) ⟩ 
     (a ∷ x) ↑≼ x 
   ≡⟨ red ⟩ 
      a ∷ x
   ≡∎)
  where red : (a ∷ x) ↑≼ x ≡ a ∷ x
        red with we? (a ∷ x) | we? x 
        red | yes ⊠ax | _ = ⊥-elim (□ax ⊠ax)
        red | no _ | yes ⊠x = ⊥-elim (□ax (we-∷ a ⊠x))
        red | no _ | no □x with width x ≤? width (a ∷ x)
        ...   | yes _ = refl
        ...   | no ax<wx = ⊥-elim (ax<wx (width-∷ a x))
        