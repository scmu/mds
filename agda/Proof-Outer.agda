module Proof-Outer where

open import Data.Empty
open import Data.Product
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
open import Properties
open import Overlap
open import Utilities

open import AlgebraicReasoning.Equality
open import AlgebraicReasoning.Implications 

gen : ∀ z x → mds x ≼ mdp (z ++ x) → mdp (z ++ x) ≡ mdp (z ++ wp x)
gen z [] = λ _ → refl
gen z (a ∷ y) = body
 where 
  body : mds (a ∷ y) ≼ mdp (z ++ a ∷ y) → 
         mdp (z ++ a ∷ y) ≡ mdp (z ++ wp (a ∷ y))
  body = ⇐-begin 
           mdp (z ++ a ∷ y) ≡ mdp (z ++ wp (a ∷ y)) 
         ⇐⟨ sym ∘ sandwich (++-⊑ z (wp⊑id (a ∷ y))) ⟩ 
           mdp (z ++ a ∷ y) ⊑ z ++ wp (a ∷ y)
         ⇐⟨ (λ e,p → subst (λ t → t ⊑ z ++ wp (a ∷ y)) 
                  (sym (induction (proj₂ e,p))) (proj₁ e,p)) ⟩ 
           (mdp (z ++ a ∷ wp y) ⊑ z ++ wp (a ∷ y) × P) 
         ⇐⟨ id ⟩ 
           (mdp (z ++ a ∷ wp y) ⊑ z ++ mdp (a ∷ wp y) × P) 
         ⇐⟨ overlap≼ {z} ╳ id ⟩
           (mdp (a ∷ wp y) ≼ mdp (z ++ a ∷ wp y) × P)
         ⇐⟨ ⟨ (λ e,p → subst (λ t → mdp (a ∷ wp y) ≼ t) 
                       (induction (proj₂ e,p))
                       (proj₁ e,p)) , 
              proj₂ ⟩  ⟩
           (mdp (a ∷ wp y) ≼ mdp (z ++ a ∷ y) × P)
         ⇐⟨ ≼-trans (mdp-⊑-≼-mono (a ∷ wp⊑id y)) ╳ id ⟩ 
           (mdp (a ∷ y) ≼ mdp (z ++ a ∷ y) × mds y ≼ mdp (z ++ a ∷ y))
         ⇐⟨ ↑≼-GC-→ ⟩ 
           (mdp (a ∷ y) ↑≼ mds y) ≼ mdp (z ++ a ∷ y) 
         ⇐⟨ id ⟩ 
           mds (a ∷ y) ≼ mdp (z ++ a ∷ y) 
         ⇐∎
    where P : Set
          P = mds y ≼ mdp (z ++ a ∷ y)
         
          induction : mds y ≼ mdp (z ++ a ∷ y) → mdp (z ++ a ∷ y) ≡ mdp (z ++ a ∷ wp y)
          induction p rewrite assoc z [ a ] y | assoc z [ a ] (wp y) 
                 = gen (z ++ a ∷ []) y p

main : ∀ x → mds x ≡ ms x
main [] = refl
main (a ∷ x) rewrite sym (main x) with we? x 
... | no □x = der
 where 
  der : mdp (a ∷ x) ↑≼ mds x ≡ wp (a ∷ x) ↑≼ mds x
  der = ≡-begin
          mdp (a ∷ x) ↑≼ mds x 
        ≡⟨ cong (λ e → mdp (a ∷ e) ↑≼ mds x) (impervity-id≡wp □x) ⟩
          mdp (a ∷ wp x) ↑≼ mds x
        ≡⟨ refl ⟩ 
          wp (a ∷ x) ↑≼ mds x 
        ≡∎
... | yes ⊠x with we? (mdp (a ∷ x)) | we? (mds x) | we? (wp (a ∷ x)) 
...   | no  □pax | _ | _ = ⊥-elim (□pax (bipartite-id→mdp (we-∷ a ⊠x)))
...   | yes ⊠pax | no □sx | _ = ⊥-elim (□sx (bipartite-id→mds ⊠x))
...   | yes ⊠pax | yes ⊠sx | no □wax = ⊥-elim (□wax (bipartite-id→wp (we-∷ a ⊠x)))
...   | yes ⊠pax | yes ⊠sx | yes ⊠wax 
          with mds x ≤d? mdp (a ∷ x)
...         | yes sx≤pax 
                rewrite sym (gen [ a ] x (≼-density ⊠sx ⊠pax sx≤pax))
                with we? (mdp (a ∷ x))
...                | no □pax  = ⊥-elim (□pax ⊠pax)
...                | yes _ with mds x ≤d? mdp (a ∷ x)
...                        | yes _ = refl
...                        | no pax<sx = ⊥-elim (pax<sx sx≤pax)
main (a ∷ x) | yes ⊠x | yes ⊠pax | yes ⊠sx | yes ⊠wax | no pax<sx 
  with mds x ≤d? wp (a ∷ x)
... | no _ = refl
... | yes sx≤wax = ⊥-elim (wax<sx sx≤wax)
  where wax<sx : wp (a ∷ x) <d mds x
        wax<sx = ≤d<d-trans 
                   (mdp-⊑-≤d-mono {a ∷ wp x} {a ∷ x} 
                       (we-∷ a (bipartite-id→wp ⊠x))
                       (a ∷ wp⊑id x)) 
                   pax<sx

{-   by inequational reasoning
        wax<sx : wp (a ∷ x) <d mds x
        wax<sx = ≤d-begin 
                  wp (a ∷ x) 
               ≤d⟨ mdp-⊑-≤d-mono {a ∷ wp x} {a ∷ x} 
                   (we-∷ a (bipartite-id→wp ⊠x)) (a ∷ wp⊑id x) ⟩ 
                  mdp (a ∷ x) 
               <d⟨ pax<sx ⟩ 
                  mds x 
               ≤d∎  
-}