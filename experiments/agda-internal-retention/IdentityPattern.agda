{-# OPTIONS --safe --without-K #-}
module IdentityPattern where
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

identity : ∀ {ℓ} {A : Set ℓ} → A → A
identity x = x

J : ∀ {a b} {A : Set a} {x : A}
    (P : (y : A) → x ≡ y → Set b) → P x refl → {y : A} (p : x ≡ y) → P y p
J P d refl = d

predecessor : Nat → Nat
predecessor zero = zero
predecessor (suc n) = n

forget : .(n : Nat) → Nat
forget _ = zero

abstract
  opaqueIdentity : ∀ {ℓ} {A : Set ℓ} → A → A
  opaqueIdentity x = x
