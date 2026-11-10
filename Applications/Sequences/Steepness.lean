import SquareKit.ListFusion

/-!
# Tupling a suffix summary with its decision

The list is steep when each entry strictly exceeds the sum of its proper suffix.
The tupled implementation carries the sum alongside the decision; its proof is
an application of the shared reachable right-fold fusion law. All values are
mathematical integers. This equality alone makes no runtime-cost claim.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Sequences.Steepness

/-- Independent suffix-decomposition specification for steepness. -/
def Steep (xs : List Int) : Prop :=
  ∀ front x back, xs = front ++ x :: back → back.sum < x

theorem steep_nil : Steep [] := by
  intro front x back h
  have := congrArg List.length h
  simp at this

theorem steep_cons_iff (x : Int) (xs : List Int) :
    Steep (x :: xs) ↔ xs.sum < x ∧ Steep xs := by
  constructor
  · intro h
    constructor
    · exact h [] x xs rfl
    · intro front y back heq
      exact h (x :: front) y back (by simp [heq])
  · rintro ⟨hx, hs⟩ front y back heq
    cases front with
    | nil =>
      have he : x = y ∧ xs = back := by simpa using heq
      rcases he with ⟨rfl, rfl⟩
      exact hx
    | cons z front =>
      have he : x = z ∧ xs = front ++ y :: back := by simpa using heq
      exact hs front y back he.2

def steep : List Int → Bool
  | [] => true
  | x :: xs => decide (xs.sum < x) && steep xs

theorem steep_correct (xs : List Int) : steep xs = true ↔ Steep xs := by
  induction xs with
  | nil => simp [steep, steep_nil]
  | cons x xs ih => simp [steep, steep_cons_iff, ih]

/-- The summary and decision use the same suffix result. -/
def tupleStep (x : Int) (state : Int × Bool) : Int × Bool :=
  (x + state.1, decide (state.1 < x) && state.2)

def fastSteep (xs : List Int) : Int × Bool := xs.foldr tupleStep (0, true)

def steepFast (xs : List Int) : Bool := (fastSteep xs).2

theorem fastSteep_invariant (xs : List Int) : fastSteep xs = (xs.sum, steep xs) := by
  have fusion := SquareKit.ListFusion.foldr_reachable List.cons tupleStep
    (fun ys : List Int => (ys.sum, steep ys)) (fun _ => True) [] trivial
    (fun _ _ _ => trivial) (fun _ _ _ => rfl) xs
  simpa [fastSteep, steep] using fusion.symm

theorem steepFast_eq_steep (xs : List Int) : steepFast xs = steep xs := by
  rw [steepFast, fastSteep_invariant]

theorem steepFast_correct (xs : List Int) : steepFast xs = true ↔ Steep xs := by
  rw [steepFast_eq_steep, steep_correct]

end Sequences.Steepness
