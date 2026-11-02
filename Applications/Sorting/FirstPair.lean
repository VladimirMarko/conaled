import Applications.Checking.OrderCertificate
import Mathlib.Data.List.Perm.Basic

/-!
# Comparing the first pair of a list

The VFA `Perm` chapter's conditional swap is factored through an arbitrary
Boolean comparator. Occurrence preservation needs no ordering laws; idempotence
needs only asymmetry of the comparator, and ordered output needs a separate
comparison contract. The unchanged tail need not be sorted.

Source: Appel, *Verified Functional Algorithms* 2.1, `Perm.v` (2026-08-24).
See `docs/research/vfa-coverage.md` for source correspondence and scope.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting

universe u v
variable {α : Type u} {β : Type v}

/-- Swap just the first two entries when the supplied comparator says to. -/
def compareSwap (swap : α → α → Bool) : List α → List α
  | a :: b :: rest => if swap a b then b :: a :: rest else a :: b :: rest
  | xs => xs

/-- The first pair is ordered; empty and singleton lists satisfy the contract. -/
def FirstPair (R : α → α → Prop) : List α → Prop
  | a :: b :: _ => R a b
  | _ => True

/-- An arbitrary comparator preserves every occurrence, including duplicates. -/
theorem compareSwap_perm (swap : α → α → Bool) (xs : List α) :
    xs.Perm (compareSwap swap xs) := by
  cases xs with
  | nil => exact List.Perm.refl _
  | cons a xs =>
    cases xs with
    | nil => exact List.Perm.refl _
    | cons b rest =>
      simp only [compareSwap]
      split
      · exact List.Perm.swap _ _ _
      · exact List.Perm.refl _

/-- Applying the comparison twice has no further effect under asymmetry. -/
theorem compareSwap_idempotent (swap : α → α → Bool)
    (asymmetric : ∀ a b, swap a b = true → swap b a = false) (xs : List α) :
    compareSwap swap (compareSwap swap xs) = compareSwap swap xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => rfl
    | cons b rest =>
      cases h : swap a b with
      | false => simp [compareSwap, h]
      | true => simp [compareSwap, h, asymmetric a b h]

theorem compareSwap_firstPair (swap : α → α → Bool) (R : α → α → Prop)
    (law : ∀ a b, (swap a b = true → R b a) ∧ (swap a b = false → R a b))
    (xs : List α) : FirstPair R (compareSwap swap xs) := by
  cases xs with
  | nil => trivial
  | cons a xs =>
    cases xs with
    | nil => trivial
    | cons b rest =>
      cases h : swap a b with
      | false => simpa [compareSwap, h, FirstPair] using (law a b).2 h
      | true => simpa [compareSwap, h, FirstPair] using (law a b).1 h

theorem compareSwap_correct (swap : α → α → Bool) (R : α → α → Prop)
    (law : ∀ a b, (swap a b = true → R b a) ∧ (swap a b = false → R a b))
    (xs : List α) : xs.Perm (compareSwap swap xs) ∧
      FirstPair R (compareSwap swap xs) :=
  ⟨compareSwap_perm swap xs, compareSwap_firstPair swap R law xs⟩

/-- The source algorithm preserves the entire suffix after the first pair. -/
theorem compareSwap_drop_two (swap : α → α → Bool) (xs : List α) :
    (compareSwap swap xs).drop 2 = xs.drop 2 := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => rfl
    | cons b rest => simp only [compareSwap]; split <;> rfl

/-- Representation maps transport the operation when they preserve comparison. -/
theorem compareSwap_map (swap : α → α → Bool) (swap' : β → β → Bool)
    (f : α → β) (law : ∀ a b, swap' (f a) (f b) = swap a b) (xs : List α) :
    compareSwap swap' (xs.map f) = (compareSwap swap xs).map f := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => rfl
    | cons b rest => simp only [List.map_cons, compareSwap, law]; split <;> rfl

theorem firstPair_iff_chain_take_two (R : α → α → Prop) (xs : List α) :
    FirstPair R xs ↔ (xs.take 2).IsChain R := by
  cases xs with
  | nil => simp [FirstPair]
  | cons a xs =>
    cases xs with
    | nil => simp [FirstPair]
    | cons b rest => simp [FirstPair, List.isChain_cons_cons]

/-- Reuse the existing ordering checker on the prefix certified by the swap.
No transitivity or ordering of the remaining suffix is assumed. -/
theorem compareSwap_checkedPrefix {α : Type} (swap check : α → α → Bool)
    (R : α → α → Prop)
    (swapLaw : ∀ a b, (swap a b = true → R b a) ∧ (swap a b = false → R a b))
    (checkLaw : ∀ a b, check a b = true ↔ R a b) (xs : List α) :
    OrderCertificate.adjacent check ((compareSwap swap xs).take 2) = true :=
  (OrderCertificate.adjacent_correct checkLaw _).mpr
    ((firstPair_iff_chain_take_two R _).mp (compareSwap_firstPair swap R swapLaw xs))

end Applications.Sorting
