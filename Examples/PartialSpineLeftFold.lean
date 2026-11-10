import Applications.Progress.SpineFolds
import Examples.PartialSpineLimits

/-!
# Available prefixes and completed-end demand

Counting and emit-once producers expose a first label, but their semantic left
fold still requires an end event that this producer interface cannot emit.
The finite cases independently distinguish known prefixes, completed lists,
accumulator argument order, and the absence of a step-monotonicity premise.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PartialSpineLeftFold

open Order SquareKit PartialSpine Progress Progress.SpineObservations PartialSpineLimits

/-- The existing first consumer succeeds on both actual realizations while left fold waits for an end. -/
theorem counting_first_and_foldl (p : Nat → Prop) (f : Prop → Nat → Prop) (e : Prop) (s : Nat) :
    first p (observations (guarded PartialSpineProgress.count) s) = p s ∧
      first p (observations (paused PartialSpineProgress.count) (false, s)) = p s ∧
      Observations.foldl f e (observations (guarded PartialSpineProgress.count) s) = False ∧
      Observations.foldl f e (observations (paused PartialSpineProgress.count) (false, s)) = False :=
  ⟨first_guarded p _ s, first_paused p _ s,
    foldl_observations _ f e s, foldl_observations _ f e (false, s)⟩

theorem once_first_and_foldl (p : Nat → Prop) (f : Prop → Nat → Prop) (e : Prop) (a : Nat) :
    first p (observations PartialSpineProgress.once (some a)) = p a ∧
      Observations.foldl f e (observations PartialSpineProgress.once (some a)) = False :=
  ⟨first_once p a, foldl_observations _ f e (some a)⟩

example (f : Prop → Nat → Prop) (e : Prop) (s : Nat) :
    Observations.foldl f e
      (observations (fun n => Sum.inr (n + 1) : Producer Nat Nat) s) = False :=
  foldl_observations _ f e s

-- Prefix availability and its exact guarded/paused transition counts are separate facts.
example :
    truncate 3 (observations (guarded PartialSpineProgress.count) 4) =
        Ideal.principal (openPrefix [4, 5, 6]) ∧
      Delivers (guarded PartialSpineProgress.count) 4 [4, 5, 6] 7 3 ∧
      Delivers (paused PartialSpineProgress.count) (false, 4) [4, 5, 6] (false, 7) 6 ∧
      Observations.foldl (fun (_ : Prop) (_ : Nat) => True) False
        (observations (guarded PartialSpineProgress.count) 4) = False := by
  refine ⟨?_, ?_, ?_, foldl_observations _ _ _ 4⟩
  · rw [truncate_guarded]
    rfl
  · exact (PartialSpineProgress.count_deliveries 4 3).1
  · exact (PartialSpineProgress.count_deliveries 4 3).2

example :
    Observations.foldl (fun (_ : Prop) (_ : Nat) => True) False
        (Ideal.principal (ofList [4, 5, 6])) = True ∧
      Observations.foldl (fun (_ : Prop) (_ : Nat) => True) False
        (Ideal.principal (openPrefix [4, 5, 6])) = False := by
  constructor
  · rw [Observations.foldl_ofList]
    rfl
  · exact Observations.foldl_openPrefix _ _ _

-- Negation is not monotone on Prop; the spine and semantic theorems still apply.
example :
    ¬ Monotone (fun P : Prop => ¬ P) ∧
      Observations.foldl (fun (P : Prop) (_ : Nat) => ¬ P) False
        (Ideal.principal (ofList [4, 5, 6])) = True ∧
      Observations.foldl (fun (P : Prop) (_ : Nat) => ¬ P) False
        (Ideal.principal (openPrefix [4, 5, 6])) = False := by
  refine ⟨?_, ?_, Observations.foldl_openPrefix _ _ _⟩
  · intro monotone
    have impossible : (¬ False) → ¬ True := monotone (show False ≤ True from False.elim)
    exact impossible (by simp) True.intro
  · simpa using
      (Observations.foldl_ofList
        (fun (P : Prop) (_ : Nat) => ¬ P) False [4, 5, 6])

-- The result is a standard left fold, with the accumulator before the element.
example : PartialSpine.foldl ([] : List Nat) (fun xs n => n :: xs) [9]
    (ofList [1, 2]) = [2, 1, 9] := by
  rw [PartialSpine.foldl_ofList]
  rfl

-- Completed input may return bottom; nonbottom necessity is not an equivalence.
example : Observations.foldl (fun (_ : Prop) (_ : Nat) => False) True
    (Ideal.principal (ofList [4])) = False := by
  rw [Observations.foldl_ofList]
  rfl

example :
    Observations.foldl (fun (_ : Prop) (_ : Nat) => False) True
        (Ideal.principal .nil) = True ∧
      Observations.foldl (fun (_ : Prop) (_ : Nat) => False) True ⊥ = False :=
  ⟨Observations.foldl_nil _ _, Observations.foldl_bottom _ _⟩

end PartialSpineLeftFold
