module Properties.Bipartite where

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
open import Properties.Impervity

open import AlgebraicReasoning.Implications 
open import AlgebraicReasoning.Equality

{- 
  Bipartite lemma
    ∀ x → width x < L ↔ width (wp x) < L ↔ width (mdp x) < L ↔ width (mds x) < L
-}

bipartite-id→mdp : ∀ {x} → we x → we (mdp x)
bipartite-id→mdp {x} ⊠x = max≼-we ∃we
  where ∃we : Any⁺ we (prefixes x)
        ∃we = ∈-pred ⊠x (id∈prefixes x)

bipartite-¬mdp→¬id : ∀ {x} → ¬(we (mdp x)) → ¬(we x)
bipartite-¬mdp→¬id □mx ⊠x = □mx (bipartite-id→mdp ⊠x)

bipartite-id→wp : ∀ {x} → we x → we (wp x)
bipartite-id→wp {[]} ⊠[] = ⊥-elim (L-positive ⊠[])
bipartite-id→wp {a ∷ x} ⊠ax = 
    (⇐-begin 
        we (wp (a ∷ x)) 
     ⇐⟨ id ⟩
        we (mdp (a ∷ wp x)) 
     ⇐⟨ bipartite-id→mdp ⟩ 
        we (a ∷ wp x) 
     ⇐∎
    ) ⊠awp
  where ⊠awp : we (a ∷ wp x)
        ⊠awp with we? x
        ... | no □x rewrite sym (impervity-id≡wp □x) = ⊠ax
        ... | yes ⊠x = we-∷ a (bipartite-id→wp ⊠x)

bipartite-id→mds : ∀ {x} → we x → we (mds x)
bipartite-id→mds {[]} ⊠[] = ⊥-elim (L-positive ⊠[])
bipartite-id→mds {a ∷ x} ⊠ax with we? x 
... | no □x = ≥-begin 
                width (mds (a ∷ x))
              ≥⟨ ≥-refl' refl ⟩
                width (mdp (a ∷ x) ↑≼ mds x) 
              ≥⟨ ≥-refl' (cong (λ e → width (mdp (a ∷ x) ↑≼ e))
                               (sym (impervity-id≡mds □x))) ⟩
                width (mdp (a ∷ x) ↑≼ x) 
              ≥⟨ ≥-refl' (cong width see-below) ⟩ 
                width (mdp (a ∷ x)) 
              ≥⟨ bipartite-id→mdp ⊠ax ⟩ 
                L 
              ≥∎
  where open ≥-reasoning
        see-below : mdp (a ∷ x) ↑≼ x ≡ mdp (a ∷ x)
        see-below with we? (mdp (a ∷ x)) | we? x 
        see-below | no □pax | _ = ⊥-elim (□pax (bipartite-id→mdp ⊠ax))
        see-below | yes _ | yes ⊠x = ⊥-elim (□x ⊠x)
        see-below | yes _ | no _ = refl
... | yes ⊠x = 
     (⇐-begin 
        we (mds (a ∷ x)) 
      ⇐⟨ id ⟩ 
        we (mdp (a ∷ x) ↑≼ mds x) 
      ⇐⟨ ↑≼-we₂ ⟩ 
       we (mds x) 
      ⇐⟨ bipartite-id→mds ⟩ 
       we x 
      ⇐∎) ⊠x
