{-# OPTIONS --safe --cubical --guardedness #-}
module HigherWitness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Homotopy.Loopspace using (Ω)
open import Cubical.ZCohomology.Base using (coHomK; coHomK-ptd; coHom-pt)
open import Cubical.ZCohomology.Properties using (Kn≃ΩKn+1∙)
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Data.Nat using (zero; suc; znots)
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Equality.Base as Eq
open import Cubical.Data.Equality.Conversion
  using (PathIsoEq; pathToEq-reflPath; eqToPath)
open import FrozenMemo

-- This semantic parameter is a 2-type; the generic memo has no HIT constructor.
A : Type₀
A = coHomK 2

x : A
x = coHom-pt 2

EqΩ : Pointed ℓ-zero → Pointed ℓ-zero
EqΩ (X , a) = (a Eq.≡ a) , Eq.refl

path-to-identity : (X : Pointed ℓ-zero) → Ω X ≡ EqΩ X
path-to-identity X = ua∙ (isoToEquiv PathIsoEq) (eqToPath pathToEq-reflPath)

-- The basepoint comparison is retained, so reflexivity is sent to zero.
abstract
  double-identities : (ℤ , pos 0) ≡ EqΩ (EqΩ (coHomK-ptd 2))
  double-identities = Kn≃ΩKn+1∙ {n = 0}
                   ∙ cong Ω (Kn≃ΩKn+1∙ {n = 1})
                   ∙ path-to-identity (Ω (coHomK-ptd 2))
                   ∙ cong EqΩ (path-to-identity (coHomK-ptd 2))

H : Type₀
H = Eq.refl {x = x} Eq.≡ Eq.refl

carrier-path : ℤ ≡ H
carrier-path = cong fst double-identities

decode : ℤ → H
decode = transport carrier-path

encode : H → ℤ
encode = transport (sym carrier-path)

encode-decode : (n : ℤ) → encode (decode n) ≡ n
encode-decode = transport⁻Transport carrier-path

decode-zero : decode (pos 0) ≡ Eq.refl
decode-zero = fromPathP (λ i → snd (double-identities i))

encode-refl : encode Eq.refl ≡ pos 0
encode-refl = sym (cong encode decode-zero) ∙ encode-decode (pos 0)

h : H
h = decode (pos 1)

encode-h : encode h ≡ pos 1
encode-h = encode-decode (pos 1)

-- A direct discriminator, without relying on a normalization claim for encode.
zero-not-one : pos 0 ≡ pos 1 → ⊥
zero-not-one p = znots (cong abs p)
  where
  abs : ℤ → _
  abs (pos n) = n
  abs _ = 0

h-not-refl : h Eq.≡ Eq.refl → ⊥
h-not-refl p = zero-not-one
  (sym encode-refl ∙ sym (cong encode (eqToPath p)) ∙ encode-h)

module PF = PathFamily A x
module M = Memo A PF.B

-- Both substituted expressions and their transported types are checked here.
w-twice-h : M.second-w (PF.input h) Eq.≡ M.valueWitness (M.σ∘τ (PF.input h))
w-twice-h = M.w-twice (PF.input h)

apd-twice-h : M.second-apd (PF.input h) Eq.≡ M.higherWitness (M.σ∘τ (PF.input h))
apd-twice-h = M.apd-twice (PF.input h)

observed : H
observed = Eq.sym (PF.β Eq.refl) Eq.∙ Eq.ap PF.T h Eq.∙ PF.β Eq.refl

observation : observed Eq.≡ h
observation = PF.observation h

observation-detects-one : encode observed ≡ pos 1
observation-detects-one = cong encode (eqToPath observation) ∙ encode-h

-- Erasing the selected second identity to reflexivity fails the same observer.
erasure-rejected : observed Eq.≡ Eq.refl → ⊥
erasure-rejected p = h-not-refl (Eq.sym observation Eq.∙ p)
