module DRSP where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Function using (_∘_; id)
open import Data.Nat
open import Data.List
open import Data.List.All

open import Relation.Nullary
open import Relation.Binary hiding (NonEmpty)

open import Relation.Binary.PropositionalEquality hiding ([_]; inspect)

open import Elem
open import List+
open import Prefix
open import MDS
open import RightSkew

open import Properties.Max

open import Utilities

open import AlgebraicReasoning.Equality
open import AlgebraicReasoning.Implications 

DRSP : List (List Elem) → Set
DRSP xs = Adj _>d_ xs × All NonEmpty xs × All RightSkew xs

[]-DRSP : DRSP []
[]-DRSP = [] , [] , []

-- DRSP unique. Not proved yet.

{-
private
 
  data PartAlign {A : Set} : List (List A) → List (List A) → Set where
   PA-l : ∀ zs xs ys
          → PartAlign (concat zs ∷ xs) (zs ++ ys)
   PA-lm : ∀ zs z y xs ys
           → PartAlign ((concat zs ++ z) ∷ y ∷ xs) (zs ++ (z ++ y) ∷ ys)
   PA-eq : ∀ x xs ys → PartAlign (x ∷ xs) (x ∷ ys)
   PA-r : ∀ zs z y xs ys
          → PartAlign (zs ++ (z ++ y) ∷ xs) ((concat zs ++ z) ∷ y ∷ ys)

  data List≡ {A : Set} : List A → List A → Set where
   [] : List≡ [] []
   _∷_ : ∀ {a b x y} → a ≡ b → x ≡ y → List≡ (a ∷ x) (b ∷ y)

  part-align : ∀ {A} (x : List A) {ys zs}
               → NonEmpty ys → NonEmpty zs
               → All NonEmpty ys → All NonEmpty zs
               → List≡ (concat ys) x → List≡ (concat zs) x
               → PartAlign ys zs
  part-align .(a ∷ _) (._ ∷ []) (._ ∷ []) ((a ∷ []) ∷ NEys) ((.a ∷ z) ∷ NEzs) 
             (refl ∷ refl) (refl ∷ eq2) rewrite r-zero-++[] {_}{z} eq2 = PA-eq (a ∷ []) [] []
  part-align .(a ∷ _) (._ ∷ []) (._ ∷ (b ∷ w) ∷ zs) ((a ∷ []) ∷ NEys) ((.a ∷ z) ∷ (.b ∷ .w) ∷ NEzs) 
             (refl ∷ refl) (refl ∷ eq2) with m-zero-++[] z (b ∷ w) _ eq2
  ...  | ()
  part-align .(a ∷ _) (._ ∷ y ∷ ys) (._ ∷ []) ((a ∷ []) ∷ NEys) ((.a ∷ z) ∷ NEzs) 
             (refl ∷ eq1) (refl ∷ eq2) = {!!}
  part-align .(a ∷ _) (._ ∷ y ∷ ys) (._ ∷ w ∷ zs) ((a ∷ []) ∷ NEys) ((.a ∷ z) ∷ NEzs) 
             (refl ∷ eq1) (refl ∷ eq2) = {!!}
  part-align .(a ∷ _) (._ ∷ ys) (._ ∷ zs) ((a ∷ y) ∷ NEys) ((.a ∷ z) ∷ NEzs) 
             (refl ∷ eq1) (refl ∷ eq2) = {!!}
-}
{-
DRSP-unique : ∀ {x ys zs} → concat ys ≡ x → concat zs ≡ x
              → DRSP ys → DRSP zs → ys ≡ zs
DRSP-unique {[]} {[]} {[]} _ _ _ _ = refl
DRSP-unique {[]} {[]} {.(a ∷ y) ∷ ys} _ () _ (_ , (a ∷ y) ∷ _ , _)
DRSP-unique {[]} {.(a ∷ x) ∷ xs} () _ (_ , (a ∷ x) ∷ _ , _) _ 
DRSP-unique {a ∷ _} {[]} {_} () _ _ _
DRSP-unique {a ∷ _} {_} {[]} _ () _ _
DRSP-unique {a ∷ []} ys≡ zs≡ (_ , (b ∷ _ ∷ _) ∷ _ , _) (_ , (c ∷ _) ∷ _ , _) with ∷-≡-hd-tl ys≡ 
... | _ , ()
DRSP-unique {a ∷ []} ys≡ zs≡ (_ , (b ∷ _) ∷ _ , _) (_ , (c ∷ _ ∷ _) ∷ _ , _) with ∷-≡-hd-tl zs≡ 
... | _ , ()
DRSP-unique {a ∷ []} ys≡ zs≡ 
   (_ , (_ ∷ []) ∷ _ , _) (_ , (_ ∷ []) ∷ _ , _) with ∷-≡-hd-tl ys≡ |  ∷-≡-hd-tl zs≡  
DRSP-unique {a ∷ []} _ _
   (_ , (.a ∷ []) ∷ NEys , _) (Dzs , (.a ∷ []) ∷ NEzs , _) | refl , ys≡ | refl , zs≡ 
  rewrite NE-concat-[] NEys ys≡ | NE-concat-[] NEzs zs≡ = refl
DRSP-unique {a ∷ b ∷ x} ys≡ zs≡ 
   (_ , (_ ∷ _) ∷ _ , _) (_ , (_ ∷ _) ∷ _ , _) with ∷-≡-hd-tl ys≡ |  ∷-≡-hd-tl zs≡  
DRSP-unique {a ∷ b ∷ x} _ _
   (Dys , (.a ∷ []) ∷ NEys , _ ∷ Rys) (Dzs , (.a ∷ []) ∷ NEzs , _ ∷ Rzs) | refl , ys≡ | refl , zs≡
  rewrite DRSP-unique {b ∷ x} ys≡ zs≡ (Adj-tl Dys , NEys , Rys) (Adj-tl Dzs , NEzs , Rzs) = refl
DRSP-unique {a ∷ b ∷ x} _ _
   (Dys , (.a ∷ []) ∷ NEys , Rys) (Dzs , (.a ∷ _ ∷ _) ∷ NEzs , Rzs) | refl , ys≡ | refl , zs≡ = {!!}
DRSP-unique {a ∷ b ∷ x} _ _
   (Dys , (.a ∷ _) ∷ NEys , Rys) (Dzs , (.a ∷ _) ∷ NEzs , Rzs) | refl , ys≡ | refl , zs≡ = {!!}

-}

-- bitonic property

 -- we can prove the following more precise property, and can 
 -- in fact use this property later. However, we need only
 -- the looser version bitonic-left'.

bitonic-left :
    ∀ z xs x → SnocWF xs
    → Adj _>d_ (xs ++ [ x ]) → All NonEmpty xs → NonEmpty x → NonEmpty z
    → z ++ concat xs <d x 
    → Adj⁺ _<d_ (map⁺ (_++_ z ∘ concat) (prefixes (xs ++ [ x ])))
bitonic-left z .[] x [] dec nex nx nz zxsy<x 
  rewrite r-id-++-[] z | r-id-++-[] x = <d→<d-++ nz nx zxsy<x ∷[·]
bitonic-left z .(xs ++ [ y ]) x (∷ʳ-wf xs sn y) dec nex nx nz zxsy<x
  rewrite prefixes-∷ʳ (xs ++ [ y ]) x
        | prefixes-∷ʳ xs y 
        | map⁺-++⁺ (_++_ z ∘ concat) (prefixes xs ++⁺ [ xs ++ [ y ] ]⁺) 
                    [ (xs ++ [ y ]) ++ [ x ] ]⁺ 
        | map⁺-++⁺ (_++_ z ∘ concat) (prefixes xs) [ xs ++ [ y ] ]⁺ 
        | concat-snoc (xs ++ [ y ]) x 
        | assoc z (concat (xs ++ [ y ])) x =
    Adj⁺-snoc (map⁺ (_++_ z ∘ concat) (prefixes xs)) 
      (z ++ concat (xs ++ [ y ])) 
      ((z ++ concat (xs ++ [ y ])) ++ x) 
      adj-init
      adj-last
  where 
    adj-last : (z ++ concat (xs ++ [ y ])) <d ((z ++ concat (xs ++ [ y ])) ++ x)
    adj-last = (<d→<d-++ (NE-++-l nz) nx zxsy<x)

    adj-init : Adj⁺ _<d_ 
          (map⁺ (_++_ z ∘ concat) (prefixes xs) ++⁺ [ z ++ concat (xs ++ [ y ]) ]⁺) 
    adj-init rewrite sym (map⁺-++⁺ (_++_ z ∘ concat) (prefixes xs) [ xs ++ [ y ] ]⁺ ) 
                   | sym (prefixes-∷ʳ xs y) = 
           bitonic-left z xs y sn (Adj-init dec) 
             (All-init nex) (All-last xs nex) nz (zxs<y z xs y zxsy<x dec nex nz) -- zxs<y
       where zxs<y : ∀ z xs y
                     → (z ++ foldr _++_ [] (xs ++ y ∷ [])) <d x
                     → Adj (λ x₁ y₁ → y₁ <d x₁) ((xs ++ y ∷ []) ++ x ∷ [])
                     → All NonEmpty (xs ++ y ∷ [])
                     → NonEmpty z
                     → (z ++ concat xs) <d y
             zxs<y z xs y zxsy<x' dec nex nz
               rewrite concat-snoc xs y
                     | assoc z (concat xs) y  =
                (⇒-begin
                   (z ++ concat xs) ++ y <d x
                 ⇒⟨ (λ m → <d-trans m (Adj-last xs dec)) ⟩
                   (z ++ concat xs) ++ y <d y
                 ⇒⟨ ++-<d→<d (NE-++-l nz) (All-last xs nex) ⟩
                   (z ++ concat xs <d y ⇒∎))
                  zxsy<x'

{- Maybe necessary for another choice of ↑d 

bitonic-left' :
    ∀ z xs x → SnocWF xs
    → Adj _>d_ (xs ++ [ x ]) → All NonEmpty xs → NonEmpty x → NonEmpty z
    → z ++ concat xs ≤d x 
    → Adj⁺ _≤d_ (map⁺ (_++_ z ∘ concat) (prefixes (xs ++ [ x ])))
bitonic-left' z .[] x [] dec nex nx nz z≤x 
  rewrite r-id-++-[] z | r-id-++-[] x = ≤d→≤d-++ nz nx z≤x ∷[·] 
bitonic-left' z .(xs ++ [ y ]) x (∷ʳ-wf xs sn y) dec nex nx nz zxsy≤x
  rewrite prefixes-∷ʳ (xs ++ [ y ]) x
        | prefixes-∷ʳ xs y 
        | map⁺-++⁺ (_++_ z ∘ concat) (prefixes xs ++⁺ [ xs ++ [ y ] ]⁺) 
                    [ (xs ++ [ y ]) ++ [ x ] ]⁺ 
        | map⁺-++⁺ (_++_ z ∘ concat) (prefixes xs) [ xs ++ [ y ] ]⁺ 
        | concat-snoc (xs ++ [ y ]) x 
        | assoc z (concat (xs ++ [ y ])) x = 
    Adj⁺-snoc (map⁺ (_++_ z ∘ concat) (prefixes xs))
      (z ++ concat (xs ++ [ y ]))
      ((z ++ concat (xs ++ [ y ])) ++ x) adj-init adj-last
  where 
    adj-last : (z ++ concat (xs ++ [ y ])) ≤d ((z ++ concat (xs ++ [ y ])) ++ x)
    adj-last = ≤d→≤d-++ (NE-++-l nz) nx zxsy≤x

    adj-init : Adj⁺ _≤d_ 
          (map⁺ (_++_ z ∘ concat) (prefixes xs) ++⁺ [ z ++ concat (xs ++ [ y ]) ]⁺) 
    adj-init rewrite sym (map⁺-++⁺ (_++_ z ∘ concat) (prefixes xs) [ xs ++ [ y ] ]⁺ ) 
                   | sym (prefixes-∷ʳ xs y) = 
             bitonic-left' z xs y sn (Adj-init dec) (All-init nex)
                   (All-last xs nex) nz zxs≤y
       where zxs≤y : (z ++ concat xs) ≤d y 
             zxs≤y with zxsy≤x 
             ... | zxsy≤x' rewrite concat-snoc xs y 
                                 | assoc z (concat xs) y = 
              (⇒-begin 
                (z ++ concat xs) ++ y ≤d x 
               ⇒⟨ (λ m → ≤d-trans m (<d→≤d (Adj-last xs dec))) ⟩ 
                (z ++ concat xs) ++ y ≤d y 
               ⇒⟨ ++-≤d→≤d (NE-++-l nz) (All-last xs nex) ⟩ 
                z ++ concat xs ≤d y ⇒∎) 
              zxsy≤x'
-}

private -- old, deprecated inspect

  data Inspect {a} {A : Set a} (x : A) : Set a where
    _with-≡_ : (y : A) (eq : x ≡ y) → Inspect x

  inspect : ∀ {a} {A : Set a} (x : A) → Inspect x
  inspect x = x with-≡ refl

maxchop-correct :
  ∀ z xs → (wf : SnocWF xs)
  → NonEmpty z → Adj _>d_ xs → All NonEmpty xs
  → z ++ concat (maxchop z xs wf) ≡ maxd (map⁺ (_++_ z ∘ concat) (prefixes xs))
maxchop-correct z .[] [] _ _ _ = refl
maxchop-correct z .(xs ++ [ x ]) (∷ʳ-wf xs wf x) nz dec nxs 
   with x ≤d? (z ++ concat xs)
... | yes x≤zxs with inspect wf
maxchop-correct z .([ x ]) (∷ʳ-wf ._ wf x) nz _ (nx ∷ _) 
  | yes x≤z | [] with-≡ eq[] 
    rewrite r-id-++-[] x | eq[] | r-id-++-[] z = sym (↑d-left zx≤z)
    where zx≤z : (z ++ x) ≤d z
          zx≤z = ≥d→≥d-++ nz nx x≤z
maxchop-correct z .((xs ++ [ y ]) ++ [ x ]) (∷ʳ-wf ._ wf x) nz dec nxs 
  | yes x≤zxsy | ∷ʳ-wf xs wf' y with-≡ p
   rewrite prefixes-∷ʳ (xs ++ [ y ]) x 
         | map⁺-++⁺ (_++_ z ∘ concat) (prefixes (xs ++ [ y ])) 
                    [ (xs ++ [ y ]) ++ [ x ] ]⁺ 
         | prefixes-∷ʳ xs y 
         | map⁺-++⁺ (_++_ z ∘ concat) (prefixes xs) 
                    [ xs ++ [ y ] ]⁺ 
   = sym body
  where body : maxd ((map⁺ (_++_ z ∘ concat) (prefixes xs) ++⁺
                        [ z ++ concat (xs ++ [ y ]) ]⁺) ++⁺
                       [ z ++ concat ((xs ++ [ y ]) ++ [ x ]) ]⁺)
                  ≡ z ++ concat (maxchop z (xs ++ [ y ]) wf)
        body = ≡-begin 
                 maxd ((map⁺ (_++_ z ∘ concat) (prefixes xs) ++⁺
                        [ z ++ concat (xs ++ [ y ]) ]⁺)
                        ++⁺ [ z ++ concat ((xs ++ [ y ]) ++ [ x ]) ]⁺)
               ≡⟨ maxd-snoc2 (map⁺ (_++_ z ∘ concat) (prefixes xs))
                   (z ++ concat (xs ++ [ y ])) 
                   (z ++ concat ((xs ++ [ y ]) ++ [ x ])) ⟩ 
                 maxd (map⁺ (_++_ z ∘ concat) (prefixes xs)) ↑d
                 ((z ++ concat (xs ++ [ y ])) ↑d 
                  (z ++ concat ((xs ++ [ y ]) ++ [ x ])))
               ≡⟨ cong (λ e → maxd (map⁺ (_++_ z ∘ concat) (prefixes xs)) ↑d e) 
                   (↑d-left zxsyx≤zxsy)  ⟩ 
                 maxd (map⁺ (_++_ z ∘ concat) (prefixes xs)) ↑d
                           (z ++ concat (xs ++ [ y ]))
               ≡⟨ sym eq₁ ⟩ 
                 maxd (map⁺ (_++_ z ∘ concat) (prefixes (xs ++ [ y ]))) 
               ≡⟨ sym (maxchop-correct z (xs ++ [ y ]) wf
                  nz (Adj-init dec) (All-init nxs))  ⟩ 
                 z ++ concat (maxchop z (xs ++ [ y ]) wf) 
               ≡∎ 
          where zxsyx≤zxsy : (z ++ concat ((xs ++ [ y ]) ++ [ x ])) ≤d 
                             (z ++ concat (xs ++ [ y ]))
                zxsyx≤zxsy rewrite concat-snoc (xs ++ [ y ]) x
                           | assoc z (concat (xs ++ [ y ])) x 
                        = ≥d→≥d-++ (NE-++-l nz) (All-last (xs ++ y ∷ []) nxs) x≤zxsy

                eq₁ : maxd (map⁺ (_++_ z ∘ concat) (prefixes (xs ++ [ y ])))
                      ≡ maxd (map⁺ (_++_ z ∘ concat) (prefixes xs)) ↑d
                           (z ++ concat (xs ++ [ y ]))
                eq₁ rewrite prefixes-∷ʳ xs y 
                     | map⁺-++⁺ (_++_ z ∘ concat) (prefixes xs) [ xs ++ [ y ] ]⁺ 
                     | maxd-snoc (map⁺ (_++_ z ∘ concat) (prefixes xs)) 
                                 (z ++ concat (xs ++ [ y ]))
                  = refl  
maxchop-correct z .(xs ++ [ x ]) (∷ʳ-wf xs wf x) nz dec nxs  | no zxs<x =
   sym (≡-begin
           maxd (map⁺ (_++_ z ∘ concat) (prefixes (xs ++ [ x ]))) 
        ≡⟨ maxd-increasing increasing {- maxd-ascend ascend -} ⟩ 
          last⁺ (map⁺ (_++_ z ∘ concat) (prefixes (xs ++ [ x ])))
        ≡⟨ eq ⟩ 
          z ++ concat (xs ++ [ x ]) 
        ≡∎)
  where increasing : Adj⁺ _<d_ (map⁺ (_++_ z ∘ concat) (prefixes (xs ++ [ x ])))
        increasing = bitonic-left z xs x wf dec 
                      (All-init nxs) (All-last xs nxs) 
                       nz zxs<x
        eq : last⁺ (map⁺ (_++_ z ∘ concat) (prefixes (xs ++ [ x ]))) 
             ≡ z ++ concat (xs ++ [ x ])
        eq rewrite prefixes-∷ʳ xs x 
            | map⁺-++⁺ (_++_ z ∘ concat) (prefixes xs) [ xs ++ [ x ] ]⁺ 
            | last⁺-++⁺ (map⁺ (λ x' → z ++ foldr _++_ [] x') (prefixes xs))
               (z ++ concat (xs ++ [ x ])) = refl 

{-
   z ++ concat xs <d x₂
 ≡ z ++ concat xs <d z ++ concat xs ++ x₂

   z ++ x₀ ++ x₁ <d x₂
 ≡ z ++ x₀ ++ x₁ <d z ++ x₀ ++ x₁ ++ x₂

   z x₀ <d z x₀ x₁ <d z x₀ x₁ x₂
 ≡ zx₀ <d x₁   ∧   zx₀x₁ <d x₂
     
      zx₀x₁ <d x₂
   ⇒   { x₁ >d x₂ } 
      zx₀x₁ <d x₁
   ≡  zx₀ <d x₁
  
   z <d x₀   ∧ zx₀ <d x₁   ∧   zx₀x₁ <d x₂

-}

maxchop-correct' :
  ∀ z xs → (wf : SnocWF xs)
  → NonEmpty z → Adj _>d_ xs → All NonEmpty xs
  → concat (maxchop z xs wf) ≡ concat (max-with (↑dzc z) (prefixes xs))
maxchop-correct' z xs wf nz dec ne 
  with maxchop-correct z xs wf nz dec ne
... | eq rewrite max-d-dzc z (prefixes xs) = ++-inj z eq


-- one particular way of building DRSP

prepend-DRSP : ∀ {x xs} → NonEmpty x → RightSkew x → DRSP xs → DRSP (prepend x xs)
prepend-DRSP {x} {[]} NEx RSx _ = [·] , NEx ∷ [] , RSx ∷ []
prepend-DRSP {x} {y ∷ xs} NEx RSx _ with x ≤d? y
prepend-DRSP {x} {y ∷ xs} NEx RSx (Dxs , NExs , RSxs) | no x>dy = x>dy ∷ Dxs , NEx ∷ NExs , RSx ∷ RSxs
prepend-DRSP {x} {y ∷ .[]} NEx RSx ([·] , NEy ∷ NExs , RSy ∷ RSxs) | yes x≤dy = 
   [·] , NE-++-l NEx ∷ [] , RightSkew-++ NEx NEy RSx RSy x≤dy ∷ []
prepend-DRSP {x} {y ∷ (z ∷ xs)} NEx RSx (y>dz ∷ Dzxs , NEy ∷ NExs , RSy ∷ RSxs) | yes x≤dy 
  = prepend-DRSP {x ++ y} {z ∷ xs} (NE-++-l NEx) (RightSkew-++ NEx NEy RSx RSy x≤dy) (Dzxs , NExs , RSxs)

addl-DRSP : ∀ a {xs} → DRSP xs → DRSP (addl a xs)
addl-DRSP a Dxs = prepend-DRSP (a ∷ []) (singleton-RS a) Dxs

addl*-DRSP : ∀ {xs} y → DRSP xs → DRSP (foldr addl xs y)
addl*-DRSP [] xs-drsp = xs-drsp
addl*-DRSP (a ∷ y) xs-drsp = addl-DRSP a (addl*-DRSP y xs-drsp)
 
drsp-DRSP : ∀ x → DRSP (drsp x)
drsp-DRSP x = addl*-DRSP x []-DRSP

postulate 
  maxchop-DRSP : ∀ z xs → DRSP xs → (wf : SnocWF xs)
                 → DRSP (maxchop z xs wf)

postulate
  concat-drsp : ∀ x → concat (drsp x) ≡ x

postulate
  drsp-uniq : ∀ xs → DRSP xs → drsp (concat xs) ≡ xs
