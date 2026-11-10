import SquareKit.PartialSpine.Limits

/-!
# Append and the visibility of a suffix

Append uses the shared continuous semantic fold. The independent finite
prefix/end view determines whether its suffix seed is reached. Open finite
prefixes and infinite streams retain their unknown ends and hide every suffix.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace SquareKit.PartialSpine.Observations

open Order

universe u v
variable {α : Type u} {B : Type v}

/-- Append by interpreting the left observations, with the right ideal as seed. -/
def append (xs ys : Observations α) : Observations α := foldr cons ys xs

theorem append_left_continuous (ys : Observations α) :
    ScottContinuous (fun xs => append xs ys) :=
  foldr_continuous cons ys cons_monotone

theorem append_right_continuous (xs : Observations α) : ScottContinuous (append xs) :=
  foldr_seed_continuous cons cons_continuous xs

@[simp] theorem append_bottom (ys : Observations α) : append ⊥ ys = ⊥ :=
  foldr_bottom cons ys cons_monotone

@[simp] theorem append_nil (ys : Observations α) : append (Ideal.principal .nil) ys = ys :=
  foldr_nil cons ys cons_monotone

theorem append_cons (a : α) (xs ys : Observations α) :
    append (cons a xs) ys = cons a (append xs ys) :=
  foldr_cons cons ys cons_monotone a (cons_continuous a) xs

theorem append_right_nil (xs : Observations α) : append xs (Ideal.principal .nil) = xs :=
  foldr_cons_identity xs

/-- The prefix/end view independently determines whether the suffix is reached. -/
theorem append_principal_eq_view (s : PartialSpine α) (ys : Observations α) :
    append (Ideal.principal s) ys =
      (view s).1.foldr cons (if (view s).2 then ys else ⊥) := by
  rw [append, foldr_principal cons ys cons_monotone, PartialSpine.foldr_eq_view]

/-- A completed finite left prefix exposes an arbitrary partial or infinite suffix. -/
theorem append_ofList_left (xs : List α) (ys : Observations α) :
    append (Ideal.principal (ofList xs)) ys = xs.foldr cons ys := by
  rw [append_principal_eq_view, view_ofList]
  rfl

theorem append_ofList (xs ys : List α) :
    append (Ideal.principal (ofList xs)) (Ideal.principal (ofList ys)) =
      Ideal.principal (ofList (xs ++ ys)) := by
  induction xs with
  | nil => exact append_nil _
  | cons a xs ih =>
    change append (Ideal.principal (.cons a (ofList xs))) _ =
      Ideal.principal (.cons a (ofList (xs ++ ys)))
    rw [← cons_principal, append_cons, ih, cons_principal]

/-- Continuous tail steps retain the interpreted suffix as the transformed seed. -/
theorem foldr_append [CompletePartialOrder B] (f : α → B → B) (e : B)
    (continuous : ∀ a, ScottContinuous (f a)) (xs ys : Observations α) :
    foldr f e (append xs ys) = foldr f (foldr f e ys) xs :=
  foldr_fusion cons f ys cons_monotone (fun a => (continuous a).monotone)
    (foldr f e) (foldr_continuous f e (fun a => (continuous a).monotone))
    (foldr_bottom f e (fun a => (continuous a).monotone))
    (fun a I => foldr_cons f e (fun b => (continuous b).monotone) a (continuous a) I) xs

theorem append_assoc (xs ys zs : Observations α) :
    append (append xs ys) zs = append xs (append ys zs) :=
  foldr_append cons zs cons_continuous xs ys

/-- An unknown end is not a completed nil: no suffix can extend this observation. -/
theorem append_openPrefix (pre : List α) (ys : Observations α) :
    append (Ideal.principal (openPrefix pre)) ys = Ideal.principal (openPrefix pre) := by
  calc
    append (Ideal.principal (openPrefix pre)) ys =
        append (Ideal.principal (openPrefix pre)) (Ideal.principal .nil) := by
      simp only [append_principal_eq_view, view_openPrefix, Bool.false_eq_true, ↓reduceIte]
    _ = _ := append_right_nil _

/-- The independent directed family of stream prefixes hides every suffix. -/
theorem append_stream (σ : Stream' α) (ys : Observations α) :
    append (stream σ) ys = stream σ := by
  have fixed : (fun xs => append xs ys) ''
      (Set.range fun n => Ideal.principal (openPrefix (σ.take n))) =
      Set.range (fun n => Ideal.principal (openPrefix (σ.take n))) := by
    rw [← Set.range_comp']
    simp only [append_openPrefix]
  have lub := append_left_continuous ys (Set.range_nonempty _)
    (stream_prefixes_directed σ) (stream_prefixes_isLUB σ)
  rw [fixed] at lub
  exact lub.unique (stream_prefixes_isLUB σ)

/-- A completed ordinary prefix connects semantic append to standard stream prepend. -/
theorem append_ofList_stream (pre : List α) (σ : Stream' α) :
    append (Ideal.principal (ofList pre)) (stream σ) =
      stream (Stream'.appendStream' pre σ) := by
  induction pre with
  | nil => exact append_nil _
  | cons a pre ih =>
    change append (Ideal.principal (.cons a (ofList pre))) (stream σ) =
      stream (Stream'.cons a (Stream'.appendStream' pre σ))
    rw [← cons_principal, append_cons, ih]
    exact (stream_cons (Stream'.cons a (Stream'.appendStream' pre σ))).symm

end SquareKit.PartialSpine.Observations
