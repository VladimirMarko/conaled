module Smoke where
open import Data.Nat using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
smoke : (1 + 1) ≡ 2
smoke = refl
