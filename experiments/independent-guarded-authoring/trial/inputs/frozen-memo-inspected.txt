{-# OPTIONS --safe --cubical --guardedness #-}
module FrozenMemo where

-- The generic derivation uses intensional inductive identity, not cubical Path.
open import Cubical.Data.Equality.Base

private variable
  a b : Level
  A : Type a

-- All motives are admitted; the reflexive equation is judgmental.
j-beta : {x : A} (P : (y : A) → x ≡ y → Type b) (d : P x refl)
       → J P d refl ≡ d
j-beta P d = refl

module Memo (A : Type a) (B : A → Type b) where
  v : {x y z : A} → x ≡ y → y ≡ z → B x → B z
  v p q u = transport B q (transport B p u)

  η : {x y z : A} (p : x ≡ y) (q : y ≡ z) (u : B x)
    → v p q u ≡ transport B (p ∙ q) u
  η refl refl u = refl

  W : {x y z : A} → x ≡ y → y ≡ z → B x → Type b
  W {z = z} p q u = Σ (B z) (λ value → value ≡ transport B (p ∙ q) u)

  w : {x y z : A} (p : x ≡ y) (q : y ≡ z) (u : B x) → W p q u
  w p q u = v p q u , η p q u

  K : {x y z : A} → y ≡ z → B x → x ≡ y → Type b
  K q u p = v p q u ≡ transport B (p ∙ q) u

  apd-η : {x y z : A} {p p′ : x ≡ y} (h : p ≡ p′)
        → (q : y ≡ z) (u : B x)
        → transport (K q u) h (η p q u) ≡ η p′ q u
  apd-η h q u = apd (λ p → η p q u) h

  record Γ : Type (ℓ-max a b) where
    constructor gamma
    field
      x y z : A
      p p′ : x ≡ y
      h : p ≡ p′
      q : y ≡ z
      u : B x

  record Δ : Type (ℓ-max a b) where
    constructor delta
    field
      x z : A
      ℓ ℓ′ : x ≡ x
      h : ℓ ≡ ℓ′
      r : x ≡ z
      u : B x

  record Θ : Type (ℓ-max a b) where
    constructor theta
    field
      x : A
      ℓ ℓ′ : x ≡ x
      h : ℓ ≡ ℓ′
      k : x ≡ x
      u : B x

  σ : Δ → Γ
  σ (delta x z ℓ ℓ′ h r u) = gamma x x z ℓ ℓ′ h r u

  τ : Θ → Δ
  τ (theta x ℓ ℓ′ h k u) = delta x x ℓ ℓ′ h k u

  σ∘τ : Θ → Γ
  σ∘τ (theta x ℓ ℓ′ h k u) = gamma x x x ℓ ℓ′ h k u

  valueWitness : (γ : Γ) → W (Γ.p γ) (Γ.q γ) (Γ.u γ)
  valueWitness γ = w (Γ.p γ) (Γ.q γ) (Γ.u γ)

  higherType : Γ → Type b
  higherType γ = transport (K (Γ.q γ) (Γ.u γ)) (Γ.h γ)
                  (η (Γ.p γ) (Γ.q γ) (Γ.u γ))
                ≡ η (Γ.p′ γ) (Γ.q γ) (Γ.u γ)

  higherWitness : (γ : Γ) → higherType γ
  higherWitness γ = apd-η (Γ.h γ) (Γ.q γ) (Γ.u γ)

  first-w : (δ : Δ) → W (Δ.ℓ δ) (Δ.r δ) (Δ.u δ)
  first-w δ = valueWitness (σ δ)

  first-apd : (δ : Δ)
    → transport (K (Δ.r δ) (Δ.u δ)) (Δ.h δ)
        (η (Δ.ℓ δ) (Δ.r δ) (Δ.u δ))
      ≡ η (Δ.ℓ′ δ) (Δ.r δ) (Δ.u δ)
  first-apd δ = higherWitness (σ δ)

  second-w : (θ : Θ) → W (Θ.ℓ θ) (Θ.k θ) (Θ.u θ)
  second-w θ = first-w (τ θ)

  second-apd : (θ : Θ)
    → transport (K (Θ.k θ) (Θ.u θ)) (Θ.h θ)
        (η (Θ.ℓ θ) (Θ.k θ) (Θ.u θ))
      ≡ η (Θ.ℓ′ θ) (Θ.k θ) (Θ.u θ)
  second-apd θ = first-apd (τ θ)

  w-twice : (θ : Θ) → second-w θ ≡ valueWitness (σ∘τ θ)
  w-twice θ = refl

  apd-twice : (θ : Θ) → second-apd θ ≡ higherWitness (σ∘τ θ)
  apd-twice θ = refl

-- Naturality includes both endpoint comparisons, in the stated order.
conjugation : (T : A → A) (β : (p : A) → T p ≡ p)
            → {p p′ : A} (h : p ≡ p′)
            → sym (β p) ∙ ap T h ∙ β p′ ≡ h
conjugation T β {p = p} refl = invL (β p)

module PathFamily (A : Type a) (x : A) where
  B : A → Type a
  B y = x ≡ y

  T : {y : A} → x ≡ y → x ≡ y
  T p = transport B p refl

  β : {y : A} (p : x ≡ y) → T p ≡ p
  β refl = refl

  observation : (h : refl {x = x} ≡ refl)
              → sym (β refl) ∙ ap T h ∙ β refl ≡ h
  observation h = conjugation T β h

  input : (h : refl {x = x} ≡ refl) → Memo.Θ A B
  input h = Memo.theta x refl refl h refl refl

  retained-w : (h : refl {x = x} ≡ refl)
             → Memo.W A B refl refl refl
  retained-w h = Memo.second-w A B (input h)

  retained-apd : (h : refl {x = x} ≡ refl)
    → transport (Memo.K A B refl refl) h (Memo.η A B refl refl refl)
      ≡ Memo.η A B refl refl refl
  retained-apd h = Memo.second-apd A B (input h)
