import Mathlib.Data.List.Destutter
import Mathlib.Data.List.DropRight

/-! Adjacent-run semantics and the equality-guarded suffix fold. -/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sequences.RunCompression

universe u v
variable {α : Type u} {β : Type v}

/-- Compare adjacent original entries, preserving every unequal boundary. -/
inductive Spec : List α → List α → Prop
  | nil : Spec [] []
  | single (x : α) : Spec [x] [x]
  | repeated {x : α} {xs out : List α} :
      Spec (x :: xs) out → Spec (x :: x :: xs) out
  | boundary {x y : α} {xs out : List α} :
      x ≠ y → Spec (y :: xs) out → Spec (x :: y :: xs) (x :: out)

/-- Mathlib's adjacent destuttering, specialized to inequality. -/
abbrev compress [DecidableEq α] (xs : List α) : List α := xs.destutter (· ≠ ·)

theorem compress_step [DecidableEq α] (x y : α) (xs : List α) :
    compress (x :: y :: xs) =
      if x = y then compress (y :: xs) else x :: compress (y :: xs) := by
  by_cases h : x = y
  · subst y; simp [compress, List.destutter_cons']
  · simp [compress, List.destutter_cons', h]

theorem compress_spec [DecidableEq α] (xs : List α) : Spec xs (compress xs) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    cases xs with
    | nil => exact .single x
    | cons y ys =>
      by_cases h : x = y
      · subst y; simpa [compress_step] using Spec.repeated ih
      · simpa [compress_step, h] using Spec.boundary h ih

theorem compress_unique [DecidableEq α] {xs out : List α} (h : Spec xs out) :
    compress xs = out := by
  induction h with
  | nil => rfl
  | single x => rfl
  | repeated _ ih => simpa [compress_step] using ih
  | boundary h _ ih => simp [compress_step, h, ih]

theorem compress_iff [DecidableEq α] (xs out : List α) :
    compress xs = out ↔ Spec xs out :=
  ⟨fun h => h ▸ compress_spec xs, compress_unique⟩

/-- The relation itself is deterministic, without an equality decision procedure. -/
theorem Spec.unique {xs out₁ out₂ : List α} (h₁ : Spec xs out₁) (h₂ : Spec xs out₂) :
    out₁ = out₂ := by
  classical
  exact (compress_unique h₁).symm.trans (compress_unique h₂)

theorem compress_head [DecidableEq α] (x : α) (xs : List α) :
    (compress (x :: xs)).head? = some x := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : x = y
    · subst y; simpa [compress_step] using ih x
    · simp [compress_step, h]

theorem compress_noAdjacent [DecidableEq α] (xs : List α) :
    (compress xs).IsChain (· ≠ ·) := List.isChain_destutter _ _

theorem compress_membership [DecidableEq α] (xs : List α) (a : α) :
    a ∈ compress xs ↔ a ∈ xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      by_cases h : x = y
      · subst y; simpa [compress_step] using ih
      · simp [compress_step, h, ih]

/-- The source suffix fold. Boolean equality is separate from its law. -/
def build [BEq α] (xs : List α) : List α :=
  xs.foldr (fun x rest => x :: rest.dropWhile (x == ·)) []

theorem build_equality_step [BEq α] [LawfulBEq α] (x y : α) (xs : List α) :
    build (x :: y :: xs) =
      if x == y then build (y :: xs) else x :: build (y :: xs) := by
  by_cases h : x = y
  · subst y; simp [build, List.dropWhile_idempotent]
  · simp [build, h]

theorem build_equality_eq_compress [DecidableEq α] [BEq α] [LawfulBEq α]
    (xs : List α) : build xs = compress xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys => simp only [build_equality_step, compress_step, ih, beq_iff_eq]

theorem build_equality_iff [BEq α] [LawfulBEq α]
    (xs out : List α) : build xs = out ↔ Spec xs out := by
  classical
  rw [build_equality_eq_compress, compress_iff]

theorem build_equality_spec [BEq α] [LawfulBEq α] (xs : List α) : Spec xs (build xs) :=
  (build_equality_iff xs _).mp rfl

theorem build_equality_head [BEq α] [LawfulBEq α] (x : α) (xs : List α) :
    (build (x :: xs)).head? = some x := by
  classical
  rw [build_equality_eq_compress, compress_head]

theorem build_equality_noAdjacent [BEq α] [LawfulBEq α]
    (xs : List α) : (build xs).IsChain (· ≠ ·) := by
  classical
  rw [build_equality_eq_compress]
  exact compress_noAdjacent xs

theorem build_equality_membership [BEq α] [LawfulBEq α]
    (xs : List α) (a : α) : a ∈ build xs ↔ a ∈ xs := by
  classical
  rw [build_equality_eq_compress, compress_membership]

theorem compress_replicate_prefix [DecidableEq α] (x : α) (k : Nat) (xs : List α) :
    compress (List.replicate (k + 1) x ++ xs) = compress (x :: xs) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append] at ih ⊢
    simpa only [compress_step, ↓reduceIte] using ih

/-- Injective relabeling preserves both equal runs and unequal boundaries. -/
theorem compress_map [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (xs : List α) :
    compress (xs.map f) = (compress xs).map f :=
  (List.map_destutter_ne xs hf).symm

/-- Transport independently certified compression through a relabeling. -/
theorem Spec.map {f : α → β} (hf : Function.Injective f)
    {xs out : List α} (h : Spec xs out) : Spec (xs.map f) (out.map f) := by
  classical
  apply (compress_iff _ _).mp
  rw [compress_map f hf, compress_unique h]

end Applications.Sequences.RunCompression
