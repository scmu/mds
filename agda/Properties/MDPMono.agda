module Properties.MDPMono where

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

open import Properties.Max public

mdp-prefix : ∀ x → mdp x ∈ prefixes x
mdp-prefix x = max≼-∈ (prefixes x)

mdp⊑id : ∀ x → mdp x ⊑ x
mdp⊑id x = prefixes-⊑ (mdp-prefix x)

mdp-⊑-mono :  ∀ {x y} → x ⊑ y → mdp x ⊑ mdp y
mdp-⊑-mono x⊑y with ⊑-decompose x⊑y
mdp-⊑-mono {x} {.(x ++ [])} x⊑y | [] , refl rewrite r-id-++-[] x = ⊑-refl
mdp-⊑-mono {x} {.(x ++ a ∷ z)} x⊑y | (a ∷ z) , refl =
 (⇐-begin 
     mdp x ⊑ mdp (x ++ a ∷ z)
  ⇐⟨ subst (λ e → mdp x ⊑ max≼ e) (sym (prefixes-decompose x a z)) ⟩ 
    mdp x ⊑ max≼ (prefixes x ++⁺ map⁺ (_++_ (x ++ [ a ])) (prefixes z))
  ⇐⟨ subst (λ e → mdp x ⊑ e) (sym (max≼-++ (prefixes x) _)) ⟩ 
    mdp x ⊑
      max≼ (prefixes x) ↑≼ max≼ (map⁺ (_++_ (x ++ [ a ])) (prefixes z))
  ⇐⟨ ↑≼-pred (λ e → mdp x ⊑ e) _ _ ⟩ 
    (mdp x ⊑ max≼ (prefixes x) ×
     mdp x ⊑ max≼ (map⁺ (_++_ (x ++ [ a ])) (prefixes z)))
   ⇐∎
  ) (⊑-refl , pref)
 where open ⊑-reasoning
       pref : mdp x ⊑ max≼ (map⁺ (_++_ (x ++ [ a ])) (prefixes z))
       pref = ⊑-begin
                max≼ (prefixes x) 
              ⊑⟨ mdp⊑id x ⟩ 
                x 
              ⊑⟨ max≼-pred (λ y → x ⊑ y) (map⁺ (_++_ (x ++ [ a ])) (prefixes z)) 
                 (map⁺-pred (_++_ (x ++ [ a ])) (λ e → x ⊑ e) 
                   (aux x a) (prefixes z)) ⟩ 
                max≼ (map⁺ (_++_ (x ++ [ a ])) (prefixes z)) 
              ⊑∎
         where aux : ∀ {A : Set} (x : List A) a y → x ⊑ (x ++ [ a ]) ++ y
               aux x a y rewrite sym (assoc x [ a ] y) = ⊑-++ x (a ∷ y) 

mdp-⊑-≼-mono :  ∀ {x y} → x ⊑ y → mdp x ≼ mdp y
mdp-⊑-≼-mono x⊑y with ⊑-decompose x⊑y
mdp-⊑-≼-mono {x} {.(x ++ [])} x⊑y | [] , refl rewrite r-id-++-[] x = ≼-refl
mdp-⊑-≼-mono {x} {.(x ++ a ∷ z)} x⊑y | (a ∷ z) , refl =
 (⇐-begin 
    mdp x ≼ mdp (x ++ a ∷ z) 
  ⇐⟨ subst (λ e → mdp x ≼ max≼ e) (sym (prefixes-decompose x a z)) ⟩ 
    mdp x ≼ max≼ (prefixes x ++⁺ map⁺ (_++_ (x ++ [ a ])) (prefixes z))
  ⇐⟨ subst (λ e → mdp x ≼ e) (sym (max≼-++ (prefixes x) _)) ⟩ 
    mdp x ≼
      (max≼ (prefixes x) ↑≼ max≼ (map⁺ (_++_ (x ++ [ a ])) (prefixes z)))
  ⇐⟨ (λ _ → ↑≼-max-l (mdp x) _) ⟩ 
     ⊤ 
  ⇐∎) tt

wp⊑id : ∀ x → wp x ⊑ x
wp⊑id [] = ⊑-refl
wp⊑id (a ∷ x) = 
   ⊑-begin 
     mdp (a ∷ wp x) 
   ⊑⟨ mdp-⊑-mono (a ∷ wp⊑id x) ⟩
     mdp (a ∷ x) 
   ⊑⟨ mdp⊑id (a ∷ x) ⟩ 
     a ∷ x 
   ⊑∎
 where open ⊑-reasoning 

wp⊑mdp : ∀ x → wp x ⊑ mdp x
wp⊑mdp [] = ⊑-refl
wp⊑mdp (a ∷ x) = 
   ⊑-begin 
     mdp (a ∷ wp x) 
   ⊑⟨ mdp-⊑-mono (a ∷ wp⊑id x) ⟩
     mdp (a ∷ x) 
   ⊑∎
 where open ⊑-reasoning 

{- mdp-++ : lots of efforts to prove, but turned out not needed.

mdp-++-base : ∀ z y → max≼ (map⁺ (_++_ z) (prefixes y)) ≡
                  (z ↑≼ max≼ (map⁺ (_++_ z) (prefixes y)))
mdp-++-base z [] rewrite r-id-++-[] z | ↑≼-idem z = refl
mdp-++-base z (a ∷ y) rewrite r-id-++-[] z = 
   sym (der (max≼ (map⁺ (_++_ z) (map⁺ (_∷_ a) (prefixes y)))))
  where der : ∀ x → z ↑≼ (z ↑≼ x) ≡ z ↑≼ x
        der x = ≡-begin 
                  z ↑≼ (z ↑≼ x) 
                ≡⟨ ↑≼-assoc ⟩ 
                  (z ↑≼ z) ↑≼ x 
                ≡⟨ cong (λ e → e ↑≼ x) (↑≼-idem z) ⟩ 
                  z ↑≼ x 
                ≡∎

mdp-++-gen : ∀ z x y 
         → max≼ (map⁺ (_++_ z) (prefixes (x ++ y))) ≡
           (max≼ (map⁺ (_++_ z) (prefixes x)) ↑≼
            max≼ (map⁺ (λ w → z ++ x ++ w) (prefixes y)))
mdp-++-gen z [] y rewrite r-id-++-[] z = mdp-++-base z y
mdp-++-gen z (a ∷ x) y rewrite r-id-++-[] z = sym der
 where 
  der : (z ↑≼ max≼ (map⁺ (_++_ z) (map⁺ (_∷_ a) (prefixes x))))
          ↑≼ max≼ (map⁺ (λ w → z ++ a ∷ x ++ w) (prefixes y))
        ≡ z ↑≼ max≼ (map⁺ (_++_ z) (map⁺ (_∷_ a) (prefixes (x ++ y))))
  der = ≡-begin 
          (z ↑≼ max≼ (map⁺ (_++_ z) (map⁺ (_∷_ a) (prefixes x)))) ↑≼
            max≼ (map⁺ (λ w → z ++ a ∷ x ++ w) (prefixes y))
        ≡⟨ cong (λ e → (z ↑≼ max≼ e) ↑≼
            max≼ (map⁺ (λ w → z ++ a ∷ x ++ w) (prefixes y)))
             (map⁺-functor (_++_ z) (_∷_ a) (prefixes x)) ⟩ 
          (z ↑≼ max≼ (map⁺ (λ w → z ++ a ∷ w) (prefixes x))) ↑≼
            max≼ (map⁺ (λ w → z ++ a ∷ x ++ w) (prefixes y))
        ≡⟨ sym ↑≼-assoc ⟩ 
          z ↑≼ (max≼ (map⁺ (λ w → z ++ a ∷ w) (prefixes x)) ↑≼
            max≼ (map⁺ (λ w → z ++ a ∷ x ++ w) (prefixes y)))
        ≡⟨ cong (λ e → z ↑≼ (max≼ e ↑≼ max≼ (map⁺ (λ w → z ++ a ∷ x ++ w) (prefixes y))))
             (map⁺-cong (λ w → z ++ a ∷ w) (λ w → (z ++ [ a ]) ++ w) 
               (++-lemma z a)
                (prefixes x)) ⟩ 
          z ↑≼ (max≼ (map⁺ (λ w → (z ++ [ a ]) ++ w) (prefixes x)) ↑≼
                max≼ (map⁺ (λ w → z ++ a ∷ x ++ w) (prefixes y)))
        ≡⟨ cong (λ e → z ↑≼
                (max≼ (map⁺ (λ w → (z ++ [ a ]) ++ w) (prefixes x)) ↑≼ max≼ e))
             (map⁺-cong (λ w → z ++ a ∷ x ++ w) (λ w → (z ++ [ a ]) ++ x ++ w) 
               (λ w → ++-lemma z a (x ++ w))
                (prefixes y)) ⟩ 
          z ↑≼ (max≼ (map⁺ (λ w → (z ++ [ a ]) ++ w) (prefixes x)) ↑≼
                max≼ (map⁺ (λ w → (z ++ [ a ]) ++ x ++ w) (prefixes y)))
        ≡⟨ cong (_↑≼_ z) (sym (mdp-++-gen (z ++ [ a ]) x y)) ⟩ 
          z ↑≼ max≼ (map⁺ (λ w → (z ++ [ a ]) ++ w) (prefixes (x ++ y)))
        ≡⟨ cong (λ e → z ↑≼ max≼ e)
           (sym (map⁺-cong (λ w → z ++ a ∷ w) (λ w → (z ++ [ a ]) ++ w) 
                (++-lemma z a)
              (prefixes (x ++ y)))) ⟩ 
          z ↑≼ max≼ (map⁺ (λ w → z ++ a ∷ w) (prefixes (x ++ y))) 
        ≡⟨ cong (λ e → z ↑≼ max≼ e) 
           (sym (map⁺-functor (_++_ z) (_∷_ a) (prefixes (x ++ y)))) ⟩ 
          z ↑≼ max≼ (map⁺ (_++_ z) (map⁺ (_∷_ a) (prefixes (x ++ y))))
        ≡∎
    where ++-lemma : ∀ {A : Set} (z : List A) a y → z ++ a ∷ y ≡ (z ++ [ a ]) ++ y
          ++-lemma [] a y = refl
          ++-lemma (b ∷ z) a y rewrite ++-lemma z a y = refl

mdp-++ : ∀ x y → mdp (x ++ y) ≡ mdp x ↑≼ max≼ (map⁺ (_++_ x) (prefixes y))
mdp-++ x y = 
  ≡-begin 
    mdp (x ++ y)
  ≡⟨ refl ⟩ 
    max≼ (prefixes (x ++ y))
  ≡⟨ cong max≼ (sym (map⁺-id (_++_ []) (λ _ → refl) (prefixes (x ++ y)))) ⟩
    max≼ (map⁺ (_++_ []) (prefixes (x ++ y)))
  ≡⟨ mdp-++-gen [] x y ⟩ 
    max≼ (map⁺ (_++_ []) (prefixes x)) ↑≼
      max≼ (map⁺ (_++_ x) (prefixes y))
  ≡⟨ cong (λ e → max≼ e ↑≼ max≼ (map⁺ (_++_ x) (prefixes y))) 
      (map⁺-id (_++_ []) (λ _ → refl) (prefixes x)) ⟩ 
    mdp x ↑≼ max≼ (map⁺ (_++_ x) (prefixes y))
  ≡∎

-}