import SquareKit.PartialSpine.Limits

/-!
# Left folds that demand a completed end

The finite recursion agrees with the existing prefix/end view. Every open
spine returns bottom, independently of its accumulator step. Its semantic
interpretation is the shared ideal extension; no order law on that step is
needed because the spine order fixes labels and completed spines are maximal.
-/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.PartialSpine

universe u v
variable {α : Type u} {B : Type v}

/-- Update through known cons cells, returning a result only at completed nil. -/
def foldl (bottom : B) (f : B → α → B) (e : B) : PartialSpine α → B
  | .bottom => bottom
  | .nil => e
  | .cons a s => foldl bottom f (f e a) s

/-- The independently defined end flag determines whether the accumulator is available. -/
theorem foldl_eq_view (bottom : B) (f : B → α → B) (e : B) (s : PartialSpine α) :
    foldl bottom f e s = if (view s).2 then (view s).1.foldl f e else bottom := by
  induction s generalizing e with
  | bottom => rfl
  | nil => rfl
  | cons a s ih =>
    change foldl bottom f (f e a) s =
      if (view s).2 then (view s).1.foldl f (f e a) else bottom
    exact ih (f e a)

theorem foldl_ofList (bottom : B) (f : B → α → B) (e : B) (xs : List α) :
    foldl bottom f e (ofList xs) = xs.foldl f e := by
  rw [foldl_eq_view, view_ofList]
  rfl

/-- Knowing finitely many labels without their completed end supplies no left-fold result. -/
theorem foldl_openPrefix (bottom : B) (f : B → α → B) (e : B) (xs : List α) :
    foldl bottom f e (openPrefix xs) = bottom := by
  rw [foldl_eq_view, view_openPrefix]
  rfl

theorem foldl_eq_bottom_of_not_total (bottom : B) (f : B → α → B) (e : B)
    (s : PartialSpine α) (notTotal : ¬ IsTotal s) : foldl bottom f e s = bottom := by
  rw [foldl_eq_view]
  exact ite_eq_right notTotal

/-- No monotonicity of the accumulator step is required by the fixed-label spine order. -/
theorem foldl_monotone [Preorder B] [OrderBot B] (f : B → α → B) (e : B) :
    Monotone (foldl ⊥ f e) := by
  intro s t h
  induction h generalizing e with
  | bottom => exact bot_le
  | nil => exact le_rfl
  | cons a _ ih => exact ih (f e a)

namespace Observations

open Order

/-- A completed observation fixes the entire ideal, using the existing finite maximality law. -/
theorem eq_principal_of_total_mem (I : Observations α) (s : PartialSpine α)
    (observed : s ∈ I) (total : IsTotal s) : I = Ideal.principal s := by
  obtain ⟨xs, rfl⟩ := (isTotal_iff_exists s).mp total
  apply le_antisymm
  · intro t ht
    obtain ⟨r, _hr, hsr, htr⟩ := I.directed (ofList xs) observed t ht
    have same : ofList xs = r := (ofList_le_iff xs r).mp hsr
    subst r
    exact htr
  · exact Ideal.principal_le_iff.mpr observed

variable [CompletePartialOrder B]

/-- Extend the finite completed-end interpreter through the one shared ideal construction. -/
noncomputable def foldl (f : B → α → B) (e : B) (I : Observations α) : B :=
  IdealCompletion.extend (PartialSpine.foldl ⊥ f e) I

theorem foldl_continuous (f : B → α → B) (e : B) : ScottContinuous (foldl f e) :=
  IdealCompletion.extend_scottContinuous (PartialSpine.foldl_monotone f e)

theorem foldl_principal (f : B → α → B) (e : B) (s : PartialSpine α) :
    foldl f e (Ideal.principal s) = PartialSpine.foldl ⊥ f e s :=
  IdealCompletion.extend_principal (PartialSpine.foldl_monotone f e) s

@[simp] theorem foldl_bottom (f : B → α → B) (e : B) : foldl f e ⊥ = ⊥ :=
  foldl_principal f e .bottom

@[simp] theorem foldl_nil (f : B → α → B) (e : B) :
    foldl f e (Ideal.principal .nil) = e := foldl_principal f e .nil

theorem foldl_cons (f : B → α → B) (e : B) (a : α) (I : Observations α) :
    foldl f e (cons a I) = foldl f (f e a) I := by
  apply IdealCompletion.continuous_ext
    ((cons_continuous a).comp (foldl_continuous f e))
    (foldl_continuous f (f e a)) (I := I)
  intro s
  change foldl f e (cons a (Ideal.principal s)) =
    foldl f (f e a) (Ideal.principal s)
  rw [cons_principal, foldl_principal, foldl_principal]
  rfl

theorem foldl_ofList (f : B → α → B) (e : B) (xs : List α) :
    foldl f e (Ideal.principal (ofList xs)) = xs.foldl f e := by
  rw [foldl_principal, PartialSpine.foldl_ofList]

theorem foldl_openPrefix (f : B → α → B) (e : B) (xs : List α) :
    foldl f e (Ideal.principal (openPrefix xs)) = ⊥ := by
  rw [foldl_principal, PartialSpine.foldl_openPrefix]

/-- Absence of a completed observation forces bottom for every accumulator step and seed. -/
theorem foldl_eq_bottom_of_no_total (f : B → α → B) (e : B) (I : Observations α)
    (noTotal : ∀ s ∈ I, ¬ IsTotal s) : foldl f e I = ⊥ := by
  apply le_antisymm
  · apply IdealCompletion.extend_le (PartialSpine.foldl_monotone f e)
    intro s hs
    rw [PartialSpine.foldl_eq_bottom_of_not_total ⊥ f e s (noTotal s hs)]
  · exact bot_le

/-- A nonbottom result requires completed finite input; the converse need not hold. -/
theorem foldl_nonbottom_requires_finite (f : B → α → B) (e : B) (I : Observations α)
    (defined : foldl f e I ≠ ⊥) : ∃ xs : List α, I = Ideal.principal (ofList xs) := by
  classical
  by_contra noFinite
  apply defined
  apply foldl_eq_bottom_of_no_total f e I
  intro s hs total
  obtain ⟨xs, rfl⟩ := (isTotal_iff_exists s).mp total
  exact noFinite ⟨xs, eq_principal_of_total_mem I (ofList xs) hs (ofList_isTotal xs)⟩

/-- An infinite stream never has a completed finite spine, even for a constant step. -/
theorem foldl_stream (f : B → α → B) (e : B) (σ : Stream' α) : foldl f e (stream σ) = ⊥ := by
  classical
  by_contra defined
  obtain ⟨xs, same⟩ := foldl_nonbottom_requires_finite f e (stream σ) defined
  exact stream_ne_principal σ (ofList xs) same

end Observations
end SquareKit.PartialSpine
