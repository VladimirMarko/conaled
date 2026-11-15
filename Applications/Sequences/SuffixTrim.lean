import Mathlib.Data.List.Basic

/-! A finite suffix-trimming fold and an independent shortest-prefix contract.
Only returned values are compared; no lazy-demand or execution-cost equivalence
between the fold and the reverse/drop implementation is asserted.
See `docs/research/adwh-finite-lists.md`. -/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sequences.SuffixTrim

universe u
variable {α : Type u}

/-- Retain the shortest prefix obtained by removing an all-true suffix.
The specification mentions only input/output decompositions and prefix order. -/
def Spec (p : α → Bool) (xs out : List α) : Prop :=
  ∃ suffix, out ++ suffix = xs ∧ (∀ x ∈ suffix, p x = true) ∧
    ∀ front back, front ++ back = xs → (∀ x ∈ back, p x = true) → out <+: front

/-- The actual source fold. A matching entry is discarded only when the whole
already-processed suffix was discarded. Matching entries inside the retained
prefix stay in their original positions. -/
def trim (p : α → Bool) (xs : List α) : List α :=
  xs.foldr (fun x ys => if p x && ys.isEmpty then [] else x :: ys) []

theorem trim_eq_reverse_dropWhile (p : α → Bool) (xs : List α) :
    trim p xs = (xs.reverse.dropWhile p).reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (if p x && (trim p xs).isEmpty then [] else x :: trim p xs) = _
    rw [ih, List.reverse_cons, List.dropWhile_append]
    cases xs.reverse.dropWhile p <;> cases hp : p x <;> simp [hp]

theorem trim_decomposition (p : α → Bool) (xs : List α) :
    trim p xs ++ (xs.reverse.takeWhile p).reverse = xs := by
  rw [trim_eq_reverse_dropWhile, ← List.reverse_append,
    List.takeWhile_append_dropWhile, List.reverse_reverse]

theorem trim_append_all (p : α → Bool) (xs suffix : List α)
    (all : ∀ x ∈ suffix, p x = true) : trim p (xs ++ suffix) = trim p xs := by
  simp only [trim_eq_reverse_dropWhile, List.reverse_append]
  rw [List.dropWhile_append_of_pos]
  intro x hx
  exact all x (List.mem_reverse.mp hx)

theorem trim_minimal (p : α → Bool) (xs front back : List α)
    (decomp : front ++ back = xs) (all : ∀ x ∈ back, p x = true) :
    trim p xs <+: front := by
  subst xs
  rw [trim_append_all p front back all]
  exact ⟨(front.reverse.takeWhile p).reverse, trim_decomposition p front⟩

theorem trim_spec (p : α → Bool) (xs : List α) : Spec p xs (trim p xs) := by
  refine ⟨(xs.reverse.takeWhile p).reverse, trim_decomposition p xs, ?_,
    trim_minimal p xs⟩
  intro x hx
  exact (List.all_eq_true.mp List.all_takeWhile) x (List.mem_reverse.mp hx)

theorem Spec.unique {p : α → Bool} {xs out₁ out₂ : List α}
    (h₁ : Spec p xs out₁) (h₂ : Spec p xs out₂) : out₁ = out₂ := by
  rcases h₁ with ⟨tail₁, eq₁, all₁, minimal₁⟩
  rcases h₂ with ⟨tail₂, eq₂, all₂, minimal₂⟩
  exact (minimal₁ out₂ tail₂ eq₂ all₂).eq_of_length_le
    (minimal₂ out₁ tail₁ eq₁ all₁).length_le

theorem trim_iff (p : α → Bool) (xs out : List α) :
    trim p xs = out ↔ Spec p xs out :=
  ⟨fun h => h ▸ trim_spec p xs, fun h => (trim_spec p xs).unique h⟩

theorem trim_idempotent (p : α → Bool) (xs : List α) :
    trim p (trim p xs) = trim p xs := by
  have h := trim_append_all p (trim p xs) ((xs.reverse.takeWhile p).reverse)
    (by
      intro x hx
      exact (List.all_eq_true.mp List.all_takeWhile) x (List.mem_reverse.mp hx))
  rw [trim_decomposition] at h
  exact h.symm

end Applications.Sequences.SuffixTrim
