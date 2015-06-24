module Properties where

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
open import Properties.MDPMono public
open import Properties.Impervity public
open import Properties.Bipartite public
       
mdp-⊑-≤d-mono : ∀ {x y} → we x
                → x ⊑ y → mdp x ≤d mdp y
mdp-⊑-≤d-mono ⊠x x⊑y = ≼→≤d (bipartite-id→mdp ⊠x) (mdp-⊑-≼-mono x⊑y)

sandwich-⊑ : ∀ {x y} → x ⊑ y → mdp y ⊑ x → mdp x ⊑ mdp y
sandwich-⊑ x⊑y _ = mdp-⊑-mono x⊑y

sandwich-⊒ : ∀ {x y} → x ⊑ y → mdp y ⊑ x → mdp y ⊑ mdp x
sandwich-⊒ x⊑y mdpy⊑x with ⊑-decompose x⊑y
sandwich-⊒ {x} {.(x ++ [])} x⊑y mdpy⊑x | [] , refl 
  rewrite r-id-++-[] x = ⊑-refl
sandwich-⊒ {x} {.(x ++ a ∷ z)} x⊑y mdpy⊑x | (a ∷ z) , refl 
  rewrite prefixes-decompose x a z
        | max≼-++ (prefixes x) (map⁺ (_++_ (x ++ [ a ])) (prefixes z))
  with ↑≼-either (mdp x) (max≼ (map⁺ (_++_ (x ++ [ a ])) (prefixes z)))
...  | inj₁ eq rewrite eq = ⊑-refl
...  | inj₂ eq rewrite eq = ⊥-elim (conf x a (prefixes z) mdpy⊑x)
 where conf : ∀ x a xs → ¬ (max≼ (map⁺ (_++_ (x ++ a ∷ [])) xs) ⊑ x)
       conf x a xs mm⊑x with max≼-pred→ (λ e → e ⊑ x) (map⁺ (_++_ (x ++ a ∷ [])) xs) mm⊑x 
       ... | y , y∈ , y⊏x 
         with map⁺-pred→ (_++_ (x ++ a ∷ [])) (λ e → e ⊑ x) y∈ y⊏x 
       ... | w , w∈ , xaw⊑x rewrite sym (assoc x [ a ] w) = ¬++-⊑ x a w xaw⊑x

sandwich : ∀ {x y} → x ⊑ y → mdp y ⊑ x 
           → mdp x ≡ mdp y
sandwich x⊑y mdpy⊑x = ⊑-≡ (sandwich-⊑ x⊑y mdpy⊑x) (sandwich-⊒ x⊑y mdpy⊑x)
