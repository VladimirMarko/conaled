{-# OPTIONS --safe --cubical --guardedness #-}
module Monodromy where

open import Cubical.Data.Equality.Base
open import Cubical.Data.Equality.S1 using (S¹; base; loop; Cover)
open import Cubical.Data.Int using (ℤ; pos; sucℤ)
open import FrozenMemo

module M = Memo S¹ Cover

-- Keep the computational bridge opaque when composing the generic laws.
abstract
  circle-loop : base ≡ base
  circle-loop = loop

  step : (n : ℤ) → transport Cover circle-loop n ≡ sucℤ n
  step n = refl

input : M.Θ
input = M.theta base circle-loop circle-loop refl (circle-loop ∙ circle-loop) (pos 0)

erased-input : M.Θ
erased-input = M.theta base refl refl refl (circle-loop ∙ circle-loop) (pos 0)

abstract
  two-steps : (n : ℤ) → transport Cover (circle-loop ∙ circle-loop) n ≡ sucℤ (sucℤ n)
  two-steps n = sym (M.η circle-loop circle-loop n)
             ∙ ap (transport Cover circle-loop) (step n)
             ∙ step (sucℤ n)

transport-three : pr₁ (M.second-w input) ≡ pos 3
transport-three = ap (transport Cover (circle-loop ∙ circle-loop)) (step (pos 0))
                ∙ two-steps (pos 1)

transport-two : pr₁ (M.second-w erased-input) ≡ pos 2
transport-two = two-steps (pos 0)

value-and-witness-twice : M.second-w input ≡ M.valueWitness (M.σ∘τ input)
value-and-witness-twice = M.w-twice input

transported-witness-twice : M.second-apd input ≡ M.higherWitness (M.σ∘τ input)
transported-witness-twice = M.apd-twice input
