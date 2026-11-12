{-# OPTIONS --safe --without-K #-}
module AgdaClient where

open import Data.Bool.Base using (Bool; false; true; not; _xor_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

-- Import and specialize the real standard-library eliminator.
choose : Bool → Bool ⊎ Bool → Bool
choose mask = [ (λ x → x xor mask) , not ]′

step : Bool → Bool ⊎ Bool → Bool × Bool
step state input = state , choose state input

run : Bool → List (Bool ⊎ Bool) → List Bool
run state [] = state ∷ []
run state (input ∷ rest) = proj₁ (step state input) ∷ run (proj₂ (step state input)) rest

inputs : List (Bool ⊎ Bool)
inputs = inj₁ false ∷ inj₁ true ∷ inj₂ false ∷ inj₂ true ∷ []

observations : List Bool
observations = map (choose false) inputs ++ map (choose true) inputs ++ run false inputs ++ run true inputs

-- This checks the diagnostic oracle in Agda, not its translation to conaled.
expected : List Bool
expected = false ∷ true ∷ true ∷ false ∷ true ∷ false ∷ true ∷ false ∷
           false ∷ false ∷ true ∷ true ∷ false ∷ true ∷ true ∷ false ∷ true ∷ false ∷ []

observations-correct : observations ≡ expected
observations-correct = refl
