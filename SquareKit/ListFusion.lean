import Mathlib.Data.List.Basic

/-!
# Fusion on reachable accumulator states

These laws use standard finite lists and arbitrary accumulator types. An
invariant restricts the commuting equation to states the fold can reach.
The provenance and statement review are in `docs/research/adwh-scan-bridge.md`.
-/

namespace SquareKit.ListFusion

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- A right fold needs the commuting equation only on invariant states. -/
theorem foldr_reachable (f : α → β → β) (g : α → γ → γ)
    (h : β → γ) (P : β → Prop) (e : β) (base : P e)
    (step : ∀ x y, P y → P (f x y))
    (law : ∀ x y, P y → h (f x y) = g x (h y)) (xs : List α) :
    h (xs.foldr f e) = xs.foldr g (h e) := by
  have invariant : ∀ ys : List α, P (ys.foldr f e) := by
    intro ys
    induction ys with
    | nil => exact base
    | cons x ys ih => exact step x _ ih
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons, law x _ (invariant xs), ih]

/-- The exact context-sensitive condition, necessary as well as sufficient. -/
theorem foldr_iff (f : α → β → β) (g : α → γ → γ) (h : β → γ) (e : β) :
    (∀ xs : List α, h (xs.foldr f e) = xs.foldr g (h e)) ↔
      (∀ x (xs : List α), h (f x (xs.foldr f e)) = g x (h (xs.foldr f e))) := by
  constructor
  · intro fusion x xs
    simpa only [List.foldr_cons, fusion xs] using fusion (x :: xs)
  · intro law xs
    induction xs <;> simp_all

/-- Inclusive scan fusion preserves every intermediate state and the seed. -/
theorem scanl_reachable (f : β → α → β) (g : γ → α → γ)
    (h : β → γ) (P : β → Prop) (e : β) (base : P e)
    (step : ∀ y x, P y → P (f y x))
    (law : ∀ y x, P y → h (f y x) = g (h y) x) (xs : List α) :
    (xs.scanl f e).map h = xs.scanl g (h e) := by
  induction xs generalizing e with
  | nil => simp
  | cons x xs ih =>
    simp only [List.scanl_cons, List.map_cons]
    rw [ih (f e x) (step e x base), law e x base]

/-- The final-state counterpart of inclusive scan fusion. -/
theorem foldl_reachable (f : β → α → β) (g : γ → α → γ)
    (h : β → γ) (P : β → Prop) (e : β) (base : P e)
    (step : ∀ y x, P y → P (f y x))
    (law : ∀ y x, P y → h (f y x) = g (h y) x) (xs : List α) :
    h (xs.foldl f e) = xs.foldl g (h e) := by
  induction xs generalizing e with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.foldl_cons, law e x base] using ih (f e x) (step e x base)

/-- The Scan Lemma with indexed prefixes, including the empty prefix. -/
theorem scanl_prefix_values (f : β → α → β) (e : β) (xs : List α) :
    xs.scanl f e =
      (List.range (xs.length + 1)).map (fun n => (xs.take n).foldl f e) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_scanl, List.getElem_map, List.getElem_range]

end SquareKit.ListFusion
