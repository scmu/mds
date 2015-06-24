module MDS-Derive where

open import Data.Empty
open import Function using (_∘_; id)
open import Data.Product
open import Data.Nat
open import Data.List

open import Relation.Nullary
open import Relation.Binary hiding (NonEmpty)

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Elem
open import List+
open import Prefix
open import MDS
open import RightSkew
open import DRSP
open import Utilities using (SnocWF; []; ∷ʳ-wf; snocWF; _╳_; foldr-++; NonEmpty)

open import AlgebraicReasoning.Equality
open import AlgebraicReasoning.ExtensionalEquality
import Proof-Outer

wp-foldr : wp ≗ foldr (λ a x → mdp (a ∷ x)) []
wp-foldr [] = refl
wp-foldr (a ∷ x) =
  ≡-begin
    wp (a ∷ x)
  ≡⟨ refl ⟩
    mdp (a ∷ wp x)
  ≡⟨ cong (mdp ∘ _∷_ a) (wp-foldr x) ⟩
   mdp (a ∷ foldr (λ a' x' → mdp (a' ∷ x')) [] x)
  ≡⟨ refl ⟩
   foldr (λ a' x' → mdp (a' ∷ x')) [] (a ∷ x)
  ≡∎

wp-wps : head⁺ ∘ wps ≗ wp
wp-wps x rewrite wp-foldr x =
  scanr⁺-head-foldr (λ a' x' → mdp (a' ∷ x')) [] x

ms-wps : ms ≗ max≼ ∘ wps
ms-wps [] = refl
ms-wps (a ∷ x) =
  ≡-begin
    wp (a ∷ x) ↑≼ ms x
  ≡⟨ cong (λ e → wp (a ∷ x) ↑≼ e) (ms-wps x) ⟩
    wp (a ∷ x) ↑≼ max≼ (wps x)
  ≡⟨ refl ⟩
    mdp (a ∷ wp x) ↑≼ max≼ (wps x)
  ≡⟨ cong (λ e → mdp (a ∷ e) ↑≼ max≼ (wps x)) (sym (wp-wps x)) ⟩
    mdp (a ∷ head⁺ (wps x)) ↑≼ max≼ (wps x)
  ≡⟨ refl ⟩
    max≼ (wps (a ∷ x))
  ≡∎

postulate w-flatten-build : wflatten ∘ wbuild ≗ id

{- All these definitions about window invariants turned out to be
   not necessary.

-- Window

  -- Just Wide Enough

data JWE : List Elem → Set where
  jwe : ∀ {x} {a} → ¬ we x → we (x ++ [ a ]) → JWE (x ++ [ a ])

data JWESplit : (List Elem × List Elem) → Set where
  impervity : ∀ {x} → ¬ we x → JWESplit (x , [])
  ready : ∀ {x} → JWE x → ∀ y → JWESplit (x , y)

postulate hsplit-JWE : ∀ x → JWESplit (hsplit x)

data WindowInv : Window → Set where
  impervity : ∀ {x} → ¬ we x → WindowInv (x , [])
  ready : ∀ {x xs} → JWE x → DRSP xs → WindowInv (x , xs)

postulate
 inv : ∀ x  →
   WindowInv
    (foldr (λ a → wmaxchop ∘ wcons a) (wbuild []) x)
-}

postulate
  hsplit-NE : ∀ a x → NonEmpty (proj₁ (hsplit (a ∷ x)))

  hsplit-nil : hsplit [] ≡ ([] , [])

  hsplit-cons : ∀ a x → hsplit (a ∷ x) ≡
                        let zx₂ = hsplit x
                            z = proj₁ zx₂
                            x₂ = proj₂ zx₂
                            z'x₁ = hsplit (a ∷ z)
                            z' = proj₁ z'x₁
                            x₁ = proj₂ z'x₁
                        in (z' , x₁ ++ x₂)

  hsplit-mdp : ∀ x → hsplit (mdp x) ≡
                     let zy = hsplit x
                         z = proj₁ zy
                         y = proj₂ zy
                     in (z , max-with (↑dz z) (prefixes y))

{- It turns out that we do not need the WindowInv at all.
   The fusion condition itself provides necessary preconditions,
   e.g. that the window is a DRSP. -}

fusion : ∀ a x  →
 {- WindowInv (wbuild x) → -}
    wbuild (mdp (a ∷ x)) ≡ (wmaxchop ∘ wcons a) (wbuild x)
fusion a x rewrite hsplit-mdp (a ∷ x) | hsplit-cons a x
   with hsplit x
... | (z' , x₂) with hsplit-NE a z'
...   | NEz with hsplit (a ∷ z')
...     | (z , x₁) = congPair z (body (snocWF (foldr addl (drsp x₂) x₁)))
  where congPair : ∀ {A : Set} {B : Set} (z : A) {x y : B} → x ≡ y → (z , x) ≡ (z , y)
        congPair _ refl = refl

   {-  What happened to the RHS after pattern matching?

       (wmaxchop ∘ wcons a ∘ wbuild) x
     =  { (z' , x₂) = hsplit x }
       wmaxchop (wcons a (z' , drsp x₂))
     =  { (z , x₁) = hsplit (a ∷ z') }
       wmaxchop (z , foldr addl (drsp x₂) x₁)
   -}
        body : let xs = foldr addl (drsp x₂) x₁
               in ((wf : SnocWF xs) →
                    drsp (max-with (↑dz z) (prefixes (x₁ ++ x₂)))
                      ≡ maxchop z xs wf)
        body wf =
          ≡-begin
             drsp (max-with (↑dz z) (prefixes (x₁ ++ x₂)))
          ≡⟨ cong (drsp ∘ max-with (↑dz z) ∘ prefixes) (sym (concat-drsp (x₁ ++ x₂))) ⟩
             drsp (max-with (↑dz z) (prefixes (concat (drsp (x₁ ++ x₂)))))
          ≡⟨ cong drsp (rightskew-discrete' z (drsp (x₁ ++ x₂))
                          NEz (proj₂ (proj₂ (drsp-DRSP (x₁ ++ x₂))))) ⟩
             drsp (concat (max-with (↑dzc z) (prefixes (drsp (x₁ ++ x₂)))))
          ≡⟨ cong (drsp ∘ concat ∘ max-with (↑dzc z) ∘ prefixes)
                (foldr-++ addl [] x₁ x₂) ⟩
             drsp (concat (max-with (↑dzc z) (prefixes (foldr addl (drsp x₂) x₁))))
          ≡⟨ cong drsp
             (sym (maxchop-correct' z (foldr addl (drsp x₂) x₁)
               wf NEz (proj₁ xs-DRSP) (proj₁ (proj₂ xs-DRSP)))) ⟩
             drsp (concat (maxchop z (foldr addl (drsp x₂) x₁) wf))
          ≡⟨ drsp-uniq (maxchop z (foldr addl (drsp x₂) x₁) wf) maxchop-xs-DRSP ⟩
             maxchop z (foldr addl (drsp x₂) x₁) wf
          ≡∎
         where xs-DRSP : DRSP (foldr addl (drsp x₂) x₁)
               xs-DRSP = addl*-DRSP x₁ (drsp-DRSP x₂)

               maxchop-xs-DRSP : DRSP (maxchop z (foldr addl (drsp x₂) x₁) wf)
               maxchop-xs-DRSP = maxchop-DRSP z _ xs-DRSP wf

{-
    wbuild (mdp (a ∷ x))
  =  { by definition }
    (id ╳ drsp) (hsplit (mdp (a ∷ x)))
  =  { hsplit-mdp, let dz = (z++)° ∘ ≤d ∘ (z++) }
    let (z , x') = hsplit (a ∷ x)
    in (id ╳ drsp) (z, max dz (prefixes x'))
  =  { hsplit-cons }
    let (z , x₂) = hsplit x
        (z , x₁) = hsplit (a ∷ z)
    in (id ╳ drsp) (z , max dz (prefixes (x₁ ++ x₂)))
  =  { concat . drsp = id }
    let (z , x₂) = hsplit x
        (z , x₁) = hsplit (a ∷ z)
    in (z , drsp (max dz (prefixes (concat (drsp (x₁ ++ x₂))))))
  =  { rightskew-discrete, dzc = concat° ∘ dz ∘ concat }
    let (z , x₂) = hsplit x
        (z , x₁) = hsplit (a ∷ z)
    in (z , drsp (concat (max dzc (prefixes (drsp (x₁ ++ x₂))))))
  =  { drsp }
    let (z , x₂) = hsplit x
        (z , x₁) = hsplit (a ∷ z)
    in (z , drsp (concat (max dzc
          (prefixes (foldr addl (drsp x₂) x₁)))))
  =  { wbuild }
    let (z , xs) = wbuild x
        (z , x₁) = hsplit (a ∷ z)
    in (z , drsp (concat (max dzc
          (prefixes (foldr addl xs x₁)))))
  =  { wcons }
    let (z , xs) = wcons a (wbuild x)
    in (z , drsp (concat (max dzc (prefixes xs))))
  =  { maxchop-correct }
    let (z , xs) = wcons a (wbuild x)
    in (z , drsp (concat (maxchop xs)))
  =  { drsp - concat - drsp cancellation }
    let (z , xs) = wcons a (wbuild x)
    in (z , maxchop z xs)
-}

-- Derivation 1. A scan version of the algorithm.

mds-scan-der : mds ≗ max≼ ∘ map⁺ wflatten ∘ scanr⁺ (λ a → wmaxchop ∘ wcons a) (wbuild [])
mds-scan-der =
  ≐-begin
    mds
  ≐⟨ Proof-Outer.main ⟩
    ms
  ≐⟨ ms-wps ⟩
    max≼ ∘ scanr⁺ (λ a x → mdp (a ∷ x)) []
  ≐⟨ cong max≼ ∘ worker-wrapper-intro ∘ scanr⁺ (λ a x → mdp (a ∷ x)) [] ⟩
    max≼ ∘ map⁺ wflatten ∘ map⁺ wbuild ∘ scanr⁺ (λ a x → mdp (a ∷ x)) []
  ≐⟨ cong (max≼ ∘ map⁺ wflatten) ∘
      map⁺-scanr⁺-fusion wbuild {λ a x → mdp (a ∷ x)}
          {λ a → wmaxchop ∘ wcons a}
           [] -- WindowInv
          fusion {- inv -}  ⟩
    max≼ ∘ map⁺ wflatten ∘ scanr⁺ (λ a → wmaxchop ∘ wcons a) (wbuild [])
  ≐∎
 where
   worker-wrapper-intro :
     ∀ x → x ≡ map⁺ wflatten (map⁺ wbuild x)
   worker-wrapper-intro x
     rewrite map⁺-functor wflatten wbuild x
           | map⁺-id (wflatten ∘ wbuild) w-flatten-build x = refl

-- Derivation 2. An inductive version.

mwp : List Elem → (List Elem × Window)
mwp [] = ([] , ([] , []))
mwp (a ∷ x) with mwp x
... | (m , w) = let u = wmaxchop (wcons a w)
                in (wflatten u ↑≼ m , u)

mwp-defn : ∀ x → mwp x ≡ (ms x , wbuild (wp x))
mwp-defn [] rewrite hsplit-nil = refl
mwp-defn (a ∷ x) with mwp-defn x
... | eq with mwp x
...      | (m , w) = sym (
  ≡-begin
    (ms (a ∷ x) , wbuild (wp (a ∷ x)))
  ≡⟨ refl ⟩
    (mdp (a ∷ wp x) ↑≼ ms x , wbuild (mdp (a ∷ wp x)))
  ≡⟨ cong (λ y → y ↑≼ ms x , wbuild (mdp (a ∷ wp x)))
       (sym (w-flatten-build _)) ⟩
    (wflatten (wbuild (mdp (a ∷ wp x))) ↑≼ ms x , wbuild (mdp (a ∷ wp x)))
  ≡⟨ refl ⟩
    let u = wbuild (mdp (a ∷ wp x))
    in (wflatten u ↑≼ ms x , u)
  ≡⟨ cong (λ u → wflatten u ↑≼ ms x , u) (fusion a (wp x)) ⟩
    let u = wmaxchop (wcons a (wbuild (wp x)))
    in (wflatten u ↑≼ ms x , u)
  ≡⟨ cong (λ m₁ → let u₁ = wmaxchop (wcons a (wbuild (wp x)))
                  in wflatten u₁ ↑≼ m₁ , u₁)
       (sym (≡-proj₁ eq)) ⟩
    let u = wmaxchop (wcons a (wbuild (wp x)))
    in (wflatten u ↑≼ m , u)
  ≡⟨ cong (λ w₁ → let u₁ = wmaxchop (wcons a w₁)
                  in wflatten u₁ ↑≼ m , u₁)
       (sym (≡-proj₂ eq)) ⟩
    let u = wmaxchop (wcons a w)
    in (wflatten u ↑≼ m , u)
  ≡∎ )
 where
     ≡-proj₁ : {A B : Set} {a₁ : A} {b₁ : B} {a₂ : A} {b₂ : B}
             → (a₁ , b₁) ≡ (a₂ , b₂) → a₁ ≡ a₂
     ≡-proj₁ refl = refl
     ≡-proj₂ : {A B : Set} {a₁ : A} {b₁ : B} {a₂ : A} {b₂ : B}
             → (a₁ , b₁) ≡ (a₂ , b₂) → b₁ ≡ b₂
     ≡-proj₂ refl = refl

mwp-der : mds ≗ proj₁ ∘ mwp
mwp-der =
    ≐-begin
       mds
    ≐⟨ Proof-Outer.main ⟩
       ms
    ≐⟨ (λ x → sym (≡-proj₁ (mwp-defn x))) ⟩
       proj₁ ∘ mwp
    ≐∎
  where
     ≡-proj₁ : {A B : Set} {p : (A × B)} → ∀ {a b}
             → p ≡ (a , b) → proj₁ p ≡ a
     ≡-proj₁ refl = refl
