
# A Summary of Theorems Proved

## MDS-Derive.agda

```
wp-foldr : wp ≗ foldr (λ a x → mdp (a ∷ x)) []

wp-wps : head⁺ ∘ wps ≗ wp

ms-wps : ms ≗ max≼ ∘ wps

postulate w-flatten-build : wflatten ∘ wbuild ≗ id

postulate
  hsplit-NE : ∀ a x → NonEmpty (proj₁ (hsplit (a ∷ x)))
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

fusion : ∀ a x  →
    wbuild (mdp (a ∷ x)) ≡ (wmaxchop ∘ wcons a) (wbuild x)

main : mds ≗ max≼ ∘ map⁺ wflatten ∘ scanr⁺ (λ a → wmaxchop ∘ wcons a) (wbuild [])
```

## Overlap.agda

```
overlap-⊏→<d : ∀ u x
               → we (mdp x)
               → u ++ mdp x ⊏ mdp (u ++ x) → mdp (u ++ x) <d mdp x

overlap≼ : ∀ {u x}
           → mdp x ≼ mdp (u ++ x)
           → mdp (u ++ x) ⊑ u ++ mdp x
```

## Proof-Outer.agda

```
gen : ∀ z x → mds x ≼ mdp (z ++ x) → mdp (z ++ x) ≡ mdp (z ++ wp x)

main : ∀ x → mds x ≡ ms x
```

## Right-Skew.agda

```
postulate
  RightSkew-++ : ∀ {x y} → RightSkew x → RightSkew y
                 → x ≤d y → RightSkew (x ++ y)

prune-either : ∀ {z x₁ x₂} → NonEmpty z → NonEmpty x₁ → NonEmpty x₂
                → x₁ ≤d x₂
                → (z ++ x₁ ≤d z) ⊎ (z ++ x₁ <d z ++ x₁ ++ x₂)

two-in-three : ∀ {z x₁ x₂} → NonEmpty z → NonEmpty x₁ → NonEmpty x₂
               → x₁ ≤d x₂
               → z ↑d ((z ++ x₁) ↑d (z ++ x₁ ++ x₂))
                 ≡ z ↑d (z ++ x₁ ++ x₂)

rightskew-prefix-cancel :
    ∀ z y x → NonEmpty z → NonEmpty y
    → RightSkewExt y x
    → z ↑d maxd (map⁺ (_++_ (z ++ y)) (prefixes x))
      ≡ z ↑d (z ++ y ++ x)

rightskew-prefix :
    ∀ z x → NonEmpty z
    → RightSkew x
    → maxd (map⁺ (_++_ z) (prefixes x)) ≡ z ↑d (z ++ x)

rightskew-discrete :
  ∀ z xs
  → NonEmpty z → All RightSkew xs
  → maxd (map⁺ (_++_ z) (prefixes (concat xs)))
    ≡ maxd (map⁺ ((_++_ z) ∘ concat) (prefixes xs))

rightskew-discrete' :
  ∀ z xs
  → NonEmpty z → All RightSkew xs
  → max-with (↑dz z) (prefixes (concat xs))
     ≡ concat (max-with (↑dzc z) (prefixes xs))
```

## DRSP.agda

```
DRSP : List (List Elem) → Set
DRSP xs = Adj _>d_ xs × All NonEmpty xs × All RightSkew xs
```

### bitonic property

We can prove the following more precise property, and can
in fact use this property later. However, we need only
the looser version `bitonic-left'`.

```
bitonic-left :
    ∀ z xs x → SnocWF xs
    → Adj _>d_ (xs ++ [ x ]) → All NonEmpty xs → NonEmpty x → NonEmpty z
    → z ++ concat xs <d x
    → Adj⁺ _<d_ (map⁺ (_++_ z ∘ concat) (prefixes (xs ++ [ x ])))

maxchop-correct :
  ∀ z xs → (wf : SnocWF xs)
  → NonEmpty z → Adj _>d_ xs → All NonEmpty xs
  → z ++ concat (maxchop z xs wf) ≡ maxd (map⁺ (_++_ z ∘ concat) (prefixes xs))

maxchop-correct' :
  ∀ z xs → (wf : SnocWF xs)
  → NonEmpty z → Adj _>d_ xs → All NonEmpty xs
  → concat (maxchop z xs wf) ≡ concat (max-with (↑dzc z) (prefixes xs))
```

One particular way of building DRSP.

```
prepend-DRSP : ∀ {x xs} → NonEmpty x → RightSkew x → DRSP xs → DRSP (prepend x xs)

addl-DRSP : ∀ a {xs} → DRSP xs → DRSP (addl a xs)

addl*-DRSP : ∀ {xs} y → DRSP xs → DRSP (foldr addl xs y)

drsp-DRSP : ∀ x → DRSP (drsp x)

postulate
  maxchop-DRSP : ∀ z xs → DRSP xs → (wf : SnocWF xs)
                 → DRSP (maxchop z xs wf)

postulate
  concat-drsp : ∀ x → concat (drsp x) ≡ x

postulate
  drsp-uniq : ∀ xs → DRSP xs → drsp (concat xs) ≡ xs
```

## Elem.Core.agda

```
postulate ≤d-refl : ∀ {x} → x ≤d x
postulate ≤d-trans : ∀ {x y z} → x ≤d y → y ≤d z → x ≤d z
postulate ≤d-total : ∀ {x y} → (x ≤d y) ⊎ (y ≤d x)

postulate
  ≤d-++→≤d : ∀ {x y} → NonEmpty x → NonEmpty y → x ≤d x ++ y → x ≤d y
  ≤d→++-≤d : ∀ {x y} → NonEmpty x → NonEmpty y → x ≤d y → x ++ y ≤d y
  ≤d→≤d-++ : ∀ {x y} → NonEmpty x → NonEmpty y → x ≤d y → x ≤d x ++ y
  ++-≤d→≤d : ∀ {x y} → NonEmpty x → NonEmpty y → x ++ y ≤d y → x ≤d y

  ≥d-++→≥d : ∀ {x y} → NonEmpty x → NonEmpty y → x ≥d x ++ y → x ≥d y
  ≥d→≥d-++ : ∀ {x y} → NonEmpty x → NonEmpty y → x ≥d y → x ≥d x ++ y

  <d→++-<d : ∀ {x y} → NonEmpty x → NonEmpty y → x <d y → x ++ y <d y
  <d→<d-++ : ∀ {x y} → NonEmpty x → NonEmpty y → x <d y → x <d x ++ y
  ++-<d→<d : ∀ {x y} → NonEmpty x → NonEmpty y → x ++ y <d y → x <d y

  >d→>d-++ : ∀ {x y} → NonEmpty x → NonEmpty y → x >d y → x >d x ++ y

postulate -- because densities are numbers
  <d→≤d : ∀ {x y} → ¬ (y ≤d x) → x ≤d y
  d-tri : ∀ {x} y {z} → x ≤d z → x ≤d y ⊎ y ≤d z
  <d-trans : ∀ {x y z} → x <d y → y <d z → x <d z
  ≤d<d-trans : ∀ {x y z} → x ≤d y → y <d z → x <d z
  <d≤d-trans : ∀ {x y z} → x <d y → y ≤d z → x <d z

postulate
  L-positive : ¬ (we [])

postulate
  we-∷ : ∀ a {x} → we x → we (a ∷ x)
  ¬we-∷ : ∀ {a x} → ¬ (we (a ∷ x)) → ¬ we x
  ¬we-snoc : ∀ {x a} → ¬ (we (x ++ a ∷ [])) → ¬ we x

  -- width-[] : ∀ x → width [] ≤ width x
  width-[] : ∀ {x} → width x ≤ width [] → x ≡ []
  width-∷ : ∀ a x →  width x ≤ width (a ∷ x)
  width-snoc : ∀ x a → ¬ (width (x ++ a ∷ []) ≤ width x) -- not good enough...

we-nonempty : ∀ {x} → we x → NonEmpty x
we-nonempty {[]} ⊠x = ⊥-elim (L-positive ⊠x)
we-nonempty {a ∷ y} ⊠x = a ∷ y

we-++ : ∀ u {x} → we x → we (u ++ x)
we-++ [] ⊠x = ⊠x
we-++ (a ∷ u) ⊠x = we-∷ a (we-++ u ⊠x)

postulate
 we-++₂ : ∀ u {x} → we x → we (x ++ u)

Assoc : ∀{A : Set} → (A → A → A) → Set
Assoc _↑_ = ∀ x y z → x ↑ (y ↑ z) ≡ (x ↑ y) ↑ z

Idem : ∀{A : Set} → (A → A → A) → Set
Idem _↑_ = ∀ x → x ↑ x ≡ x

postulate
  ↑d-assoc : ∀ x y z → x ↑d (y ↑d z) ≡ (x ↑d y) ↑d z

↑d-idem : ∀ x → x ↑d x ≡ x

↑d-left : ∀ {x y} → y ≤d x → x ↑d y ≡ x

↑d-right : ∀ {x y} → x <d y → x ↑d y ≡ y
```

↑d-distr holds without side-conditions

```
↑d-distr : ∀ z x y
           → z ↑d (x ↑d y) ≡ (z ↑d x) ↑d (z ↑d y)

↑dz : List Elem → List Elem → List Elem → List Elem
↑dz z x y with (z ++ y) ≤d? (z ++ x)
... | yes y≤dx = x
... | no y>dx = y

↑dzc : List Elem → List (List Elem) → List (List Elem) → List (List Elem)
↑dzc z xs ys with (z ++ concat ys) ≤d? (z ++ concat xs)
... | yes y≤dx = xs
... | no y>dx = ys
```

## Elem.Maximum.agda


```
[]-↑≼-id : ∀ x → [] ↑≼ x ≡ x

[]-↑≼-id x | no _ | yes _ = refl

↑≼-max-l : ∀ x y → x ≼ (x ↑≼ y)

↑≼-we₁ : ∀ {x y} → we x → we (x ↑≼ y)

↑≼-we₂ : ∀ {x y} → we y → we (x ↑≼ y)

↑≼-assoc : ∀ {x y z} → x ↑≼ (y ↑≼ z) ≡ (x ↑≼ y) ↑≼ z

↑≼-idem : ∀ x → x ↑≼ x ≡ x

↑≼-either' : ∀ x y →
  ((x ↑≼ y ≡ x) × (y ≼ x)) ⊎
  ((x ↑≼ y ≡ y) × (x ≺ y))

↑≼-either : ∀ x y → (x ↑≼ y ≡ x) ⊎ (x ↑≼ y ≡ y)

↑≼-pred : (P : List Elem → Set)
          → ∀ x y → (P x × P y) → P (x ↑≼ y)

↑≼-GC-→ : ∀ {x y z} → (x ↑≼ y) ≼ z → (x ≼ z × y ≼ z)

≺-max : ∀ {x y z} → (x ↑≼ y) ≺ z → (x ≺ z × y ≺ z)
```

## Elem.Preceq.agda

```
≼-refl : ∀ {x} → x ≼ x

≼-trans : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z

<d→≺ : ∀ {x y} → we x → we y → ¬ (y ≤d x) → x ≺ y

≼→≤d : ∀ {x y} → we x → x ≼ y → x ≤d y

postulate
  ≺→<d : ∀ {x y} → we x → x ≺ y → x <d y

≼-≺-trans : ∀ {x y z} → x ≼ y → y ≺ z → x ≺ z
```

## Properties.agda

```
mdp-⊑-≤d-mono : ∀ {x y} → we x
                → x ⊑ y → mdp x ≤d mdp y

sandwich-⊑ : ∀ {x y} → x ⊑ y → mdp y ⊑ x → mdp x ⊑ mdp y

sandwich-⊒ : ∀ {x y} → x ⊑ y → mdp y ⊑ x → mdp y ⊑ mdp x

sandwich : ∀ {x y} → x ⊑ y → mdp y ⊑ x
           → mdp x ≡ mdp y
```
