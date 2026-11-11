{-# OPTIONS --safe --without-K #-}
module Core where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties
open import Data.Vec using (Vec; []; _∷_; map; _++_; replicate; take; drop; lookup; tabulate)
open import Data.Vec.Properties using (map-++; take++drop≡id; lookup∘tabulate; tabulate∘lookup)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

V : ℕ → Set
V n = Vec ℕ n

-- The alternative finite encoding is checked in both directions, pointwise
-- for functions. These are the pinned stdlib lookup/tabulation theorems.
toCoordinates : ∀ {n} → V n → Fin n → ℕ
toCoordinates = lookup
fromCoordinates : ∀ {n} → (Fin n → ℕ) → V n
fromCoordinates = tabulate
coordinates-roundtrip : ∀ {n} (f : Fin n → ℕ) i → toCoordinates (fromCoordinates f) i ≡ f i
coordinates-roundtrip = lookup∘tabulate
vector-roundtrip : ∀ {n} (x : V n) → fromCoordinates (toCoordinates x) ≡ x
vector-roundtrip = tabulate∘lookup

zeros : ∀ n → V n
zeros n = replicate n 0
add : ∀ {n} → V n → V n → V n
add [] [] = []
add (x ∷ xs) (y ∷ ys) = (x + y) ∷ add xs ys
scale : ∀ {n} → ℕ → V n → V n
scale c = map (c *_)
-- Dot is the finite sum of coordinate products, recursing over all n entries.
dot : ∀ {n} → V n → V n → ℕ
dot [] [] = 0
dot (a ∷ as) (x ∷ xs) = a * x + dot as xs
Mat : ℕ → ℕ → Set
Mat n m = Vec (V n) m
act : ∀ {n m} → Mat n m → V n → V m
act a x = map (λ row → dot row x) a
combine : ∀ {n m} → V m → Mat n m → V n
combine {n} [] [] = zeros n
combine (b ∷ bs) (a ∷ as) = add (scale b a) (combine bs as)
compose : ∀ {n m k} → Mat m k → Mat n m → Mat n k
compose b a = map (λ row → combine row a) b
identity : ∀ n → Mat n n
identity zero = []
identity (suc n) = (1 ∷ zeros n) ∷ map (0 ∷_) (identity n)
left : ∀ n m → Mat (n + m) n
left n m = map (_++ zeros m) (identity n)
right : ∀ n m → Mat (n + m) m
right n m = map (zeros n ++_) (identity m)

shuffle : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
shuffle a b c d = trans (+-assoc a b (c + d)) (trans (cong (a +_) (sym (+-assoc b c d))) (trans (cong (λ t → a + (t + d)) (+-comm b c)) (trans (cong (a +_) (+-assoc c b d)) (sym (+-assoc a c (b + d))))))
dot-zero : ∀ {n} (x : V n) → dot (zeros n) x ≡ 0
dot-zero [] = refl
dot-zero (x ∷ xs) = dot-zero xs
dot-add : ∀ {n} (a b x : V n) → dot (add a b) x ≡ dot a x + dot b x
dot-add [] [] [] = refl
dot-add (a ∷ as) (b ∷ bs) (x ∷ xs) = trans (cong₂ _+_ (*-distribʳ-+ x a b) (dot-add as bs xs)) (shuffle (a * x) (b * x) (dot as xs) (dot bs xs))
dot-scale : ∀ {n} c (a x : V n) → dot (scale c a) x ≡ c * dot a x
dot-scale c [] [] = sym (*-zeroʳ c)
dot-scale c (a ∷ as) (x ∷ xs) = trans (cong₂ _+_ (*-assoc c a x) (dot-scale c as xs)) (sym (*-distribˡ-+ c (a * x) (dot as xs)))
dot-combine : ∀ {n m} (b : V m) (a : Mat n m) x → dot (combine b a) x ≡ dot b (act a x)
dot-combine [] [] x = dot-zero x
dot-combine (b ∷ bs) (a ∷ as) x = trans (dot-add (scale b a) (combine bs as) x) (cong₂ _+_ (dot-scale b a x) (dot-combine bs as x))
act-compose : ∀ {n m k} (b : Mat m k) (a : Mat n m) x → act (compose b a) x ≡ act b (act a x)
act-compose [] a x = refl
act-compose (b ∷ bs) a x = cong₂ _∷_ (dot-combine b a x) (act-compose bs a x)
act-zero-prefix : ∀ {n m} (a : Mat n m) z x → act (map (0 ∷_) a) (z ∷ x) ≡ act a x
act-zero-prefix [] z x = refl
act-zero-prefix (a ∷ as) z x = cong (dot a x ∷_) (act-zero-prefix as z x)
act-identity : ∀ {n} (x : V n) → act (identity n) x ≡ x
act-identity [] = refl
act-identity (x ∷ xs) = cong₂ _∷_ (trans (cong₂ _+_ (*-identityˡ x) (dot-zero xs)) (+-identityʳ x)) (trans (act-zero-prefix (identity _) x xs) (act-identity xs))

dot-append : ∀ {n m} (a x : V n) (b y : V m) → dot (a ++ b) (x ++ y) ≡ dot a x + dot b y
dot-append [] [] b y = refl
dot-append (a ∷ as) (x ∷ xs) b y = trans (cong (a * x +_) (dot-append as xs b y)) (sym (+-assoc (a * x) (dot as xs) (dot b y)))
act-left-rows : ∀ {n m k} (a : Mat n k) (x : V n) (y : V m) → act (map (_++ zeros m) a) (x ++ y) ≡ act a x
act-left-rows [] x y = refl
act-left-rows (a ∷ as) x y = cong₂ _∷_ (trans (dot-append a x (zeros _) y) (trans (cong (dot a x +_) (dot-zero y)) (+-identityʳ (dot a x)))) (act-left-rows as x y)
act-right-rows : ∀ {n m k} (a : Mat m k) (x : V n) (y : V m) → act (map (zeros n ++_) a) (x ++ y) ≡ act a y
act-right-rows [] x y = refl
act-right-rows (a ∷ as) x y = cong₂ _∷_ (trans (dot-append (zeros _) x a y) (cong (_+ dot a y) (dot-zero x))) (act-right-rows as x y)
act-left : ∀ {n m} (x : V n) (y : V m) → act (left n m) (x ++ y) ≡ x
act-left x y = trans (act-left-rows (identity _) x y) (act-identity x)
act-right : ∀ {n m} (x : V n) (y : V m) → act (right n m) (x ++ y) ≡ y
act-right x y = trans (act-right-rows (identity _) x y) (act-identity y)
act-pair : ∀ {n m k} (a : Mat n m) (b : Mat n k) x → act (a ++ b) x ≡ act a x ++ act b x
act-pair a b x = map-++ (λ row → dot row x) a b

split : ∀ {n m} → V (n + m) → V n × V m
split {n} x = take n x , drop n x
join : ∀ {n m} → V n × V m → V (n + m)
join (x , y) = x ++ y
split-join : ∀ {n m} (p : V n × V m) → split (join p) ≡ p
split-join ([] , y) = refl
split-join (x ∷ xs , y) = cong (λ p → x ∷ proj₁ p , proj₂ p) (split-join (xs , y))
join-split : ∀ {n m} (x : V (n + m)) → join (split {n} {m} x) ≡ x
join-split {n} = take++drop≡id n
