{-# OPTIONS --safe --without-K #-}
module Task1 where

open import Core public
open import Data.Nat using (ℕ; _+_)
open import Data.Vec using ([]; _++_; take; drop)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Level using (0ℓ)
import Felix.Raw as R
import Felix.Laws as L
open import Felix.Homomorphism
import Felix.MakeLawful as ML
open import Felix.Instances.Function 0ℓ

record Dim (n m : ℕ) : Set where
  constructor dim
  field run : V n → V m
open Dim public

instance
  dimensions : R.Products ℕ
  dimensions = record { ⊤ = 0 ; _×_ = _+_ }
  dimCategory : R.Category Dim
  dimCategory = record { id = dim (λ x → x) ; _∘_ = λ g f → dim (λ x → run g (run f x)) }
  dimCartesian : R.Cartesian Dim
  dimCartesian = record
    { ! = dim (λ _ → [])
    ; _▵_ = λ f g → dim (λ x → run f x ++ run g x)
    ; exl = dim (take _)
    ; exr = dim (drop _)
    }
  dimObjects : Homomorphismₒ ℕ (Set 0ℓ)
  dimObjects = record { Fₒ = V }
  dimMap : Homomorphism Dim _⇾_
  dimMap = record { Fₘ = run }
  dimEquiv : Equivalent 0ℓ Dim
  dimEquiv = H-equiv
  dimFunctor : CategoryH Dim _⇾_
  dimFunctor = record { F-cong = λ p → p ; F-id = λ _ → refl ; F-∘ = λ _ → refl }
  dimProducts : ProductsH ℕ _⇾_
  dimProducts = record { ε = λ _ → [] ; ε⁻¹ = λ _ → tt ; μ = join ; μ⁻¹ = split }
  dimStrong : StrongProductsH ℕ _⇾_
  dimStrong = record
    { ε⁻¹∘ε = λ _ → refl
    ; ε∘ε⁻¹ = λ { [] → refl }
    ; μ⁻¹∘μ = split-join
    ; μ∘μ⁻¹ = join-split
    }
  dimCartesianH : CartesianH Dim _⇾_
  dimCartesianH = record
    { F-! = λ _ → refl
    ; F-▵ = λ _ → refl
    ; F-exl = λ p → cong proj₁ (split-join p)
    ; F-exr = λ p → cong proj₂ (split-join p)
    }
  dimLaws : L.Category Dim
  dimLaws = ML.LawfulCategoryᶠ Dim _⇾_
  dimCartesianLaws : L.Cartesian Dim
  dimCartesianLaws = ML.LawfulCartesianᶠ Dim _⇾_

instance
  matCategory : R.Category Mat
  matCategory = record { id = identity _ ; _∘_ = compose }
  matCartesian : R.Cartesian Mat
  matCartesian = record { ! = [] ; _▵_ = _++_ ; exl = left _ _ ; exr = right _ _ }
  matObjects : Homomorphismₒ ℕ ℕ
  matObjects = id-Hₒ
  matMap : Homomorphism Mat Dim
  matMap = record { Fₘ = λ a → dim (act a) }
  matEquiv : Equivalent 0ℓ Mat
  matEquiv = H-equiv
  matFunctor : CategoryH Mat Dim
  matFunctor = record { F-cong = λ p → p ; F-id = act-identity ; F-∘ = λ { {g = b} {f = a} → act-compose b a } }
  matProducts : ProductsH ℕ Dim
  matProducts = id-ProductsH
  matStrong : StrongProductsH ℕ Dim
  matStrong = id-StrongProductsH

mat-left : ∀ {n m} (x : V (n + m)) → act (left n m) x ≡ take n x
mat-left {n} {m} x = trans (cong (act (left n m)) (Relation.Binary.PropositionalEquality.sym (join-split {n} {m} x))) (act-left (take n x) (drop n x))
mat-right : ∀ {n m} (x : V (n + m)) → act (right n m) x ≡ drop n x
mat-right {n} {m} x = trans (cong (act (right n m)) (Relation.Binary.PropositionalEquality.sym (join-split {n} {m} x))) (act-right (take n x) (drop n x))

instance
  matCartesianH : CartesianH Mat Dim
  matCartesianH = record
    { F-! = λ _ → refl
    ; F-▵ = λ { {f = a} {g = b} → act-pair a b }
    ; F-exl = mat-left
    ; F-exr = mat-right
    }
  matLaws : L.Category Mat
  matLaws = ML.LawfulCategoryᶠ Mat Dim
  matCartesianLaws : L.Cartesian Mat
  matCartesianLaws = ML.LawfulCartesianᶠ Mat Dim

-- Checked public-law specializations: no direct matrix associativity proof.
transported-assoc : ∀ {a b c d} (f : Mat a b) (g : Mat b c) (h : Mat c d) x → act (compose (compose h g) f) x ≡ act (compose h (compose g f)) x
transported-assoc f g h = L.Category.assoc matLaws {f = f} {g} {h}
transported-projection : ∀ {a b c} (f : Mat a b) (g : Mat a c) x → act (compose (left b c) (f ++ g)) x ≡ act f x
transported-projection f g = L.Cartesian.exl∘▵ matCartesianLaws {f = f} {g}
