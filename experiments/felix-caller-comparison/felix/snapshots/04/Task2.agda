{-# OPTIONS --safe --without-K #-}
module Task2 where

open import Task1 public
open import Data.Nat using (ℕ; _+_)
open import Data.Vec using (_++_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Level using (0ℓ)
open import Felix.Homomorphism
open import Felix.Instances.Function 0ℓ

-- Public composition constructs the functor and comparison. Its source
-- object map reduces to V because the matrix-to-dimension map is identity.
compositeMap : Homomorphism Mat _⇾_
compositeMap = dimMap ∘H matMap
compositeFunctor : CategoryH Mat _⇾_ ⦃ H = compositeMap ⦄
compositeFunctor = dimFunctor ∘-CategoryH matFunctor
compositeProducts : ProductsH ℕ _⇾_
compositeProducts = compose-ProductsH
  ⦃ Fₒ = matObjects ⦄ ⦃ Fᵐ = matMap ⦄
  ⦃ Gₒ = dimObjects ⦄ ⦃ Gᵐ = dimMap ⦄
  ⦃ pH₁ = matProducts ⦄ ⦃ pH₂ = dimProducts ⦄
compositeStrong : StrongProductsH ℕ _⇾_ ⦃ pH = compositeProducts ⦄
compositeStrong = dimStrong
compositeCartesian : CartesianH Mat _⇾_ ⦃ H = compositeMap ⦄ ⦃ pH = compositeProducts ⦄
compositeCartesian = _∘-CartesianH_
  ⦃ Fₒ = matObjects ⦄ ⦃ Fᵐ = matMap ⦄
  ⦃ Gₒ = dimObjects ⦄ ⦃ Gᵐ = dimMap ⦄
  ⦃ pH₁ = matProducts ⦄ ⦃ pH₂ = dimProducts ⦄
  dimCartesianH matCartesianH

composite-action : ∀ {n m} (a : Mat n m) x → Homomorphism.Fₘ compositeMap a x ≡ act a x
composite-action a x = refl
composite-composition : ∀ {n m k} (b : Mat m k) (a : Mat n m) x → Homomorphism.Fₘ compositeMap (compose b a) x ≡ act b (act a x)
composite-composition b a = CategoryH.F-∘ compositeFunctor {g = b} {f = a}
composite-comparison : ∀ {n m} (x : V n) (y : V m) → ProductsH.μ compositeProducts (x , y) ≡ x ++ y
composite-comparison x y = refl
composite-observations : ∀ {n m k} (a : Mat n m) (b : Mat n k) x → split (Homomorphism.Fₘ compositeMap (a ++ b) x) ≡ (act a x , act b x)
composite-observations a b = CartesianH.F-▵′ compositeCartesian ⦃ spH = compositeStrong ⦄ {f = a} {g = b}
composite-left : ∀ {n m} (x : V n) (y : V m) → Homomorphism.Fₘ compositeMap (left n m) (ProductsH.μ compositeProducts (x , y)) ≡ x
composite-left x y = CartesianH.F-exl compositeCartesian (x , y)
composite-right : ∀ {n m} (x : V n) (y : V m) → Homomorphism.Fₘ compositeMap (right n m) (ProductsH.μ compositeProducts (x , y)) ≡ y
composite-right x y = CartesianH.F-exr compositeCartesian (x , y)
