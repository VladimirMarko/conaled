{-# OPTIONS --safe --without-K #-}
module Task3 where

open import Task2 public
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Nat.Properties using (+-identityʳ; *-distribˡ-+)
open import Data.Vec using ([]; _∷_; take; drop)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
open import Level using (0ℓ)
import Felix.Raw as Raw
open import Felix.Homomorphism
open import Felix.Instances.Function 0ℓ
import Felix.Construct.Comma as Comma

instance
  matrixTypeFunctor : CategoryH Mat _⇾_
  matrixTypeFunctor = compositeFunctor
  matrixTypeCartesian : CartesianH Mat _⇾_
  matrixTypeCartesian = compositeCartesian
  typeIdentityObjects : Homomorphismₒ (Set 0ℓ) (Set 0ℓ)
  typeIdentityObjects = id-Hₒ
  typeIdentityMap : Homomorphism _⇾_ _⇾_
  typeIdentityMap = id-H
  typeIdentityFunctor : CategoryH _⇾_ _⇾_
  typeIdentityFunctor = id-CategoryH
  typeIdentityProducts : ProductsH (Set 0ℓ) _⇾_
  typeIdentityProducts = id-ProductsH
  typeIdentityStrong : StrongProductsH (Set 0ℓ) _⇾_
  typeIdentityStrong = id-StrongProductsH
  typeIdentityCartesian : CartesianH _⇾_ _⇾_
  typeIdentityCartesian = id-CartesianH

module C = Comma _⇾_ Mat _⇾_

double : ∀ {n} → V n → V n
double = scale 2
object : ℕ → C.Obj
object n = C.mkᵒ {n} {V n} double

shear swap : V 2 → V 2
shear (x ∷ y ∷ []) = (x + y) ∷ y ∷ []
swap (x ∷ y ∷ []) = y ∷ x ∷ []
shearMatrix swapMatrix : Mat 2 2
shearMatrix = (1 ∷ 1 ∷ []) ∷ (0 ∷ 1 ∷ []) ∷ []
swapMatrix = (0 ∷ 1 ∷ []) ∷ (1 ∷ 0 ∷ []) ∷ []
shear-action : ∀ x → act shearMatrix x ≡ shear x
shear-action (x ∷ y ∷ []) rewrite +-identityʳ x | +-identityʳ y = refl
swap-action : ∀ x → act swapMatrix x ≡ swap x
swap-action (x ∷ y ∷ []) rewrite +-identityʳ x | +-identityʳ y = refl
shear-double : ∀ x → double (shear x) ≡ shear (double x)
shear-double (x ∷ y ∷ []) = cong₂ _∷_ (*-distribˡ-+ 2 x y) refl
swap-double : ∀ x → double (swap x) ≡ swap (double x)
swap-double (x ∷ y ∷ []) = refl

L R : C._↬_ (object 2) (object 2)
L = C.mkᵐ shearMatrix shear (λ x → trans (cong double (shear-action x)) (shear-double x))
R = C.mkᵐ swapMatrix swap (λ x → trans (cong double (swap-action x)) (swap-double x))
RL LR : C._↬_ (object 2) (object 2)
RL = C.comma-cat.comp R L
LR = C.comma-cat.comp L R

-- Semantic square statements are public comma record projections.
RL-square : ∀ x → double (act (C._↬_.f₁ RL) x) ≡ C._↬_.f₂ RL (double x)
RL-square = C._↬_.↻ RL
LR-square : ∀ x → double (act (C._↬_.f₁ LR) x) ≡ C._↬_.f₂ LR (double x)
LR-square = C._↬_.↻ LR
RL-function : ∀ x y → C._↬_.f₂ RL (x ∷ y ∷ []) ≡ y ∷ (x + y) ∷ []
RL-function x y = refl
LR-function : ∀ x y → C._↬_.f₂ LR (x ∷ y ∷ []) ≡ (y + x) ∷ x ∷ []
LR-function x y = refl
RL-matrix : ∀ x → act (C._↬_.f₁ RL) x ≡ C._↬_.f₂ RL x
RL-matrix x = trans (composite-composition swapMatrix shearMatrix x) (trans (cong (act swapMatrix) (shear-action x)) (swap-action (shear x)))
LR-matrix : ∀ x → act (C._↬_.f₁ LR) x ≡ C._↬_.f₂ LR x
LR-matrix x = trans (composite-composition shearMatrix swapMatrix x) (trans (cong (act shearMatrix) (swap-action x)) (shear-action (swap x)))
forward-example : act (C._↬_.f₁ RL) (1 ∷ 2 ∷ []) ≡ 2 ∷ 3 ∷ []
forward-example = RL-matrix (1 ∷ 2 ∷ [])
reverse-example : act (C._↬_.f₁ LR) (1 ∷ 2 ∷ []) ≡ 3 ∷ 1 ∷ []
reverse-example = LR-matrix (1 ∷ 2 ∷ [])

module P = C.comma-products
product : ℕ → ℕ → C.Obj
product n m = Raw.Products._×_ P.products (object n) (object m)
product-connector : ∀ n m (x : V (n + m)) → C.Obj.h (product n m) x ≡ (double (take n x) , double (drop n x))
product-connector n m x = refl
projectionL : ∀ n m → C._↬_ (product n m) (object n)
projectionL n m = P.exl′
projectionR : ∀ n m → C._↬_ (product n m) (object m)
projectionR n m = P.exr′
product-left-square : ∀ n m (x : V (n + m)) → double (act (C._↬_.f₁ (projectionL n m)) x) ≡ proj₁ (C.Obj.h (product n m) x)
product-left-square n m = C._↬_.↻ (projectionL n m)
product-right-square : ∀ n m (x : V (n + m)) → double (act (C._↬_.f₁ (projectionR n m)) x) ≡ proj₂ (C.Obj.h (product n m) x)
product-right-square n m = C._↬_.↻ (projectionR n m)
product-left-matrix : ∀ n m (x : V (n + m)) → act (C._↬_.f₁ (projectionL n m)) x ≡ take n x
product-left-matrix n m = mat-left
product-right-matrix : ∀ n m (x : V (n + m)) → act (C._↬_.f₁ (projectionR n m)) x ≡ drop n x
product-right-matrix n m = mat-right
product-left-function : ∀ n m (x : V n) (y : V m) → C._↬_.f₂ (projectionL n m) (x , y) ≡ x
product-left-function n m x y = refl
product-right-function : ∀ n m (x : V n) (y : V m) → C._↬_.f₂ (projectionR n m) (x , y) ≡ y
product-right-function n m x y = refl

-- The nonidentity connector is also exercised at a closed input.
doubling-example : double (1 ∷ 2 ∷ []) ≡ 2 ∷ 4 ∷ []
doubling-example = refl
