module Overlap where

open import Data.Empty
open import Data.Product
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
open import Properties
open import Utilities

open import AlgebraicReasoning.Equality
open import AlgebraicReasoning.Implications 

private 
 postulate
   <d-++→<d' : ∀ {x b y} → we x → x <d x ++ (b ∷ y) → x <d (b ∷ y)
   <d→++-<d' : ∀ {x b y} → we x → x <d (b ∷ y) → x ++ b ∷ y <d b ∷ y


 ≤d-++→≤d' : ∀ {x b y} → we x → x ≤d x ++ (b ∷ y) → x ≤d (b ∷ y)
 ≤d-++→≤d' {x} {b} {y} ⊠x ≤d = ≤d-++→≤d (we-nonempty ⊠x) (b ∷ y) ≤d

 ≤d→++-≤d' : ∀ {x b y} → we x → x ≤d (b ∷ y) → x ++ b ∷ y ≤d b ∷ y
 ≤d→++-≤d' {x} {b} {y} ⊠x ≤d = -- with we-nonempty ⊠x
 -- ≤d→++-≤d' {._} {b} {y} ⊠x ≤d | a , x' , refl = 
   ≤d→++-≤d (we-nonempty ⊠x) (b ∷ y) ≤d

 ++-≤d→≤d' : ∀ {a x y} → we y →  a ∷ x ++ y ≤d y → a ∷ x ≤d y 
 ++-≤d→≤d' {a} {x} {y} ⊠y ≤d = -- with we-nonempty ⊠y
 -- ++-≤d→≤d' {a} {x} {._} ⊠y ≤d | b , y' , refl =
   ++-≤d→≤d (a ∷ x) (we-nonempty ⊠y) ≤d

 ≥d-++→≥d' : ∀ {a x y} → we x → x ≥d x ++ (a ∷ y) → x ≥d a ∷ y
 ≥d-++→≥d' {a} {x} {y} ⊠x ≥d = 
    ≥d-++→≥d (we-nonempty ⊠x) (a ∷ y) ≥d

{-
 An algebraic proof of overlap-⊏→<d

    u ++ mdp x ⊏ mdp (u ++ x)
 =>  { decomposition, z non-empty }
    mdp (u ++ x) = u ++ mdp x ++ z
 =>  { mdp (u ++ x) maximum }
    u ++ mdp x <d u ++ mdp x ++ z
 =>  { <d }
    u ++ mdp x <d z
 =>  { <d }
    u ++ mdp x ++ z <d z
 =>  { a ∷ z ≤d mdp x, see below }
    u ++ mdp x ++ z <d mdp x    

For z ≤d mdp x

    mdp x ++ z ≤d mdp x   -- mds x maximum 
 =>  { ≤d }
    z ≤d mdp x  
-}

overlap-⊏→<d : ∀ u x 
               → we (mdp x)
               → u ++ mdp x ⊏ mdp (u ++ x) → mdp (u ++ x) <d mdp x
overlap-⊏→<d u x ⊠mx umx⊏mux = body max₁
  where max₁ : (u ++ mdp x) <d mdp (u ++ x)
        max₁ = ≺→<d (we-++ u ⊠mx) 
               (prefix-≺ Choose-Left-↑≼ (u ++ mdp x) (u ++ x) umx⊏mux)

        open import AlgebraicReasoning.Implications 

        body : (u ++ mdp x) <d mdp (u ++ x)
               → mdp (u ++ x) <d mdp x
        body with mdp-prefix (u ++ x)
        body | mux∈ with ⊏-decompose umx⊏mux
        body | mux∈ | a , z , eq rewrite eq =
          ⇒-begin 
             u ++ mdp x  <d  (u ++ mdp x) ++ a ∷ z 
          ⇒⟨ <d-++→<d' (we-++ u ⊠mx) ⟩ 
             u ++ mdp x  <d  a ∷ z 
          ⇒⟨ <d→++-<d' (we-++ u ⊠mx) ⟩ 
            (u ++ mdp x) ++ a ∷ z  <d  a ∷ z 
          ⇒⟨ (λ <d₁ → <d≤d-trans <d₁ z≤dmx) ⟩ 
            (u ++ mdp x) ++ a ∷ z  <d  mdp x
          ⇒∎
         where max₂ : mdp x ++ a ∷ z ≤d mdp x
               max₂ = ≼→≤d (we-++₂ _ ⊠mx) 
                        (max≼-maximum (prefixes x) 
                          (++-prefixes← u 
                            (subst (λ e → e ∈ prefixes (u ++ x)) 
                              (sym (assoc u (mdp x) (a ∷ z))) mux∈))) 

               z≤dmx : (a ∷ z) ≤d mdp x
               z≤dmx = ≥d-++→≥d' {a} {mdp x} {z} ⊠mx max₂

overlap≼ : ∀ {u x} 
           → mdp x ≼ mdp (u ++ x)
           → mdp (u ++ x) ⊑ u ++ mdp x
overlap≼ {u} {x} (≼-initial □mx □mux wd) 
  rewrite sym (impervity-id≡mdp {x} (bipartite-¬mdp→¬id □mx)) 
        | sym (impervity-id≡mdp {u ++ x} (bipartite-¬mdp→¬id □mux)) = ⊑-refl
overlap≼ {u} {x} (≼-triv □mx ⊠mux)
 rewrite sym (impervity-id≡mdp {x} (bipartite-¬mdp→¬id □mx)) = mdp⊑id (u ++ x)
overlap≼ {u} {x} (≼-density ⊠mx ⊠mux mx≤mux) = 
   prefix-⊐-⊑ (mdp⊑id (u ++ x)) (++-⊑ u (mdp⊑id x)) (contra mx≤mux)
 where contra : (mdp x) ≤d (mdp (u ++ x)) →  ¬ (u ++ mdp x ⊏ mdp (u ++ x))
       contra = contrapositive' (overlap-⊏→<d u x ⊠mx)
