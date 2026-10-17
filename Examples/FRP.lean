import Applications.FRP.Spec
import Applications.FRP.Equivalence
import Squares

/-! Checked uses of the historical FRP specifications and the square interface. -/
noncomputable section

namespace Examples.FRP

/-- Here the represented carrier is a mathematical event, not a runtime. -/
def eventRep (A : Type) : Squares.Rep where
  R := FRP.OldEvent ℝ A
  S := FRP.Batch ℝ A
  decode := FRP.OldEvent.group

def mapSquare {A B : Type} (f : A → B) :
    Squares.Square (eventRep A) (eventRep B) where
  impl := FRP.OldEvent.map f
  spec := FRP.Batch.map f
  commutes := fun e => FRP.OldEvent.group_map e f

/-- Map preservation composes through the repository's existing square API. -/
theorem map_twice {A B C : Type} (f : A → B) (g : B → C)
    (e : FRP.OldEvent ℝ A) :
    (e.map f |>.map g).group = FRP.Batch.map g (FRP.Batch.map f e.group) :=
  (Squares.compose (mapSquare g) (mapSquare f)).commutes e

/-- At the change time itself, strict switching still returns the initial value. -/
theorem switch_at_change :
    FRPSpec.Event.switcher (fun _ => (3 : ℕ))
      (FRPSpec.Event.once 2 (fun _ => 7)) 2 = 3 := by
  have empty : FRPSpec.PastSupport
      (FRPSpec.Event.once 2 (fun _ : ℝ => (7 : ℕ))).at 2 = ∅ := by
    ext s
    by_cases h : s = 2
    · subst s
      simp [FRPSpec.PastSupport]
    · simp [FRPSpec.PastSupport, FRPSpec.Event.once, h]
  simp [FRPSpec.Event.switcher, FRPSpec.Event.past, empty]

/-- Simultaneous occurrences retain input order and multiplicity. -/
theorem ordered_batch :
    (FRPSpec.Event.merge (FRPSpec.Event.once 2 (3 : ℕ))
      (FRPSpec.Event.once 2 7)).at 2 = [3, 7] := by
  simp [FRPSpec.Event.merge, FRPSpec.Event.once]

end Examples.FRP
