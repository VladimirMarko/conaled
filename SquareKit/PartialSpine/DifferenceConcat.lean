import SquareKit.PartialSpine.LeftFold
import SquareKit.PartialSpine.Concat

/-!
# Concatenation through a function accumulator

The accumulator lives in the existing full function CPO. Its strict outer
left fold returns a function only after observing a completed outer end. On
finite outer lists it agrees with right-fold concatenation for arbitrary inner
ideals; an infinite outer stream instead yields the constant-bottom function.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace SquareKit.PartialSpine.Observations

open Order
open scoped SquareKit.DirectedLimits

universe u
variable {α : Type u}

/-- Accumulate append functions strictly, then supply the completed empty tail. -/
def concatD (xss : Observations (Observations α)) : Observations α :=
  foldl (fun h xs ys => h (append xs ys)) id xss (Ideal.principal .nil)

/-- Composition order is retained for every initial function and final tail. -/
theorem difference_foldl_apply (xss : List (Observations α))
    (h : Observations α → Observations α) (ys : Observations α) :
    xss.foldl (fun k xs zs => k (append xs zs)) h ys = h (xss.foldr append ys) := by
  induction xss generalizing h with
  | nil => rfl
  | cons xs xss ih => exact ih (fun zs => h (append xs zs))

/-- Only the outer list must be completed and finite; its inner labels are arbitrary. -/
theorem concatD_ofList (xss : List (Observations α)) :
    concatD (Ideal.principal (ofList xss)) = concat (Ideal.principal (ofList xss)) := by
  rw [concatD, foldl_ofList, difference_foldl_apply]
  exact (foldr_ofList append (Ideal.principal .nil)
    (fun xs => (append_right_continuous xs).monotone) xss).symm

/-- Infinite outer input makes the actual accumulated function bottom, for every seed. -/
theorem difference_foldl_stream (σ : Stream' (Observations α))
    (h : Observations α → Observations α) :
    foldl (fun k xs ys => k (append xs ys)) h (stream σ) =
      (⊥ : Observations α → Observations α) :=
  foldl_stream _ h σ

theorem concatD_stream (σ : Stream' (Observations α)) : concatD (stream σ) = ⊥ := by
  rw [concatD, difference_foldl_stream]
  rfl

/-- The strict outer fold loses even an observable infinite first inner value. -/
theorem concatD_infinite_disagrees (σ : Stream' α) :
    concatD (stream (fun _ => stream σ)) = ⊥ ∧
      concat (stream (fun _ => stream σ)) = stream σ ∧
      concatD (stream (fun _ => stream σ)) ≠ concat (stream (fun _ => stream σ)) := by
  have left := concatD_stream (fun _ => stream σ)
  have right : concat (stream (fun _ => stream σ)) = stream σ :=
    (congrArg concat (stream_cons (fun _ => stream σ))).trans
      (concat_infinite_first σ _)
  refine ⟨left, right, ?_⟩
  intro same
  exact stream_ne_principal σ .bottom (right.symm.trans (same.symm.trans left))

@[simp] theorem concatD_bottom : concatD (⊥ : Observations (Observations α)) = ⊥ := by
  rw [concatD, foldl_bottom]
  rfl

@[simp] theorem concatD_nil :
    concatD (Ideal.principal (.nil : PartialSpine (Observations α))) = Ideal.principal .nil := by
  rw [concatD, foldl_nil]
  rfl

end SquareKit.PartialSpine.Observations
