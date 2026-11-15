import Mathlib.Data.List.Infix

/-!
# Fusion on reachable accumulator states

These laws use standard finite lists and arbitrary accumulator types. An
invariant restricts the commuting equation to states the fold can reach.
The provenance and statement review are in `docs/research/adwh-scan-bridge.md`.
The suffix extensions and their clients are recorded in
`docs/research/adwh-suffix-scans.md`.
The standard prefix/suffix equations and finite source correspondences are in
`docs/research/adwh-finite-correspondence.md`.
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

/-- Standard prefixes in order, from the empty prefix to the whole list. -/
theorem inits_eq_range_take (xs : List α) :
    xs.inits = (List.range (xs.length + 1)).map (fun n => xs.take n) := by
  apply List.ext_getElem
  · simp only [List.length_inits, List.length_map, List.length_range]
  · intro i hi hj
    simp only [List.getElem_inits, List.getElem_map, List.getElem_range]

/-- Standard suffixes in order, from the whole list to the empty suffix. -/
theorem tails_eq_range_drop (xs : List α) :
    xs.tails = (List.range (xs.length + 1)).map (fun n => xs.drop n) := by
  apply List.ext_getElem
  · simp only [List.length_tails, List.length_map, List.length_range]
  · intro i hi hj
    simp only [List.getElem_tails, List.getElem_map, List.getElem_range]

/-- The Scan Lemma with indexed prefixes, including the empty prefix. -/
theorem scanl_prefix_values (f : β → α → β) (e : β) (xs : List α) :
    xs.scanl f e =
      (List.range (xs.length + 1)).map (fun n => (xs.take n).foldl f e) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_scanl, List.getElem_map, List.getElem_range]

/-- The literal prefix Scan Lemma, for any seed and accumulator type. -/
theorem foldl_inits_eq_scanl (f : β → α → β) (e : β) (xs : List α) :
    xs.inits.map (List.foldl f e) = xs.scanl f e := by
  rw [inits_eq_range_take, List.map_map]
  exact (scanl_prefix_values f e xs).symm

/-- The right Scan Lemma, ordered from the whole list to the empty suffix.
In particular, the final element is the supplied seed. -/
theorem scanr_suffix_values (f : α → β → β) (e : β) (xs : List α) :
    xs.scanr f e =
      (List.range (xs.length + 1)).map (fun n => (xs.drop n).foldr f e) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_scanr, List.getElem_map, List.getElem_range]

/-- All suffix states commute with an interpretation whose law holds only on
the invariant reached from the seed. No algebraic laws on either step are needed. -/
theorem scanr_reachable (f : α → β → β) (g : α → γ → γ)
    (h : β → γ) (P : β → Prop) (e : β) (base : P e)
    (step : ∀ x y, P y → P (f x y))
    (law : ∀ x y, P y → h (f x y) = g x (h y)) (xs : List α) :
    (xs.scanr f e).map h = xs.scanr g (h e) := by
  rw [scanr_suffix_values, scanr_suffix_values, List.map_map]
  apply List.map_congr_left
  intro n _
  exact foldr_reachable f g h P e base step law (xs.drop n)

/-- The source equation uses the standard ordered list of suffixes. -/
theorem foldr_tails_eq_scanr (f : α → β → β) (e : β) (xs : List α) :
    xs.tails.map (List.foldr f e) = xs.scanr f e := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.tails, List.map_cons, List.scanr_cons, ih]

/-- Accumulating append functions preserves every tail and arbitrary final
observation. The result type need not be a list, and `observe` needs no laws. -/
theorem foldl_append_functions (observe : List α → β)
    (blocks : List (List α)) (tail : List α) :
    (blocks.foldl (fun f xs => fun ys => f (xs ++ ys)) observe) tail =
      observe (blocks.flatten ++ tail) := by
  induction blocks generalizing observe with
  | nil => rfl
  | cons xs blocks ih =>
    simpa only [List.foldl_cons, List.flatten_cons, List.append_assoc] using
      ih (fun ys => observe (xs ++ ys))

end SquareKit.ListFusion
