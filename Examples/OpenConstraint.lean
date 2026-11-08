import SquareKit.OpenConstraint

namespace Examples.OpenConstraint
open SquareKit.OpenConstraint

def flip : Network Bool Bool where
  Internal := Unit
  accepts a _ b := b = !a

theorem flip_behavior (a b : Bool) : behavior flip a b ↔ b = !a := by
  simp [behavior, flip]

/-- Joining two independently constrained stages recovers the input. -/
theorem two_flips (a b : Bool) : behavior (compose flip flip) a b ↔ b = a := by
  rw [behavior_compose]
  simp only [flip_behavior]
  constructor
  · rintro ⟨c, rfl, rfl⟩
    simp
  · intro h
    exact ⟨!a, rfl, by simpa using h⟩

/-- A concrete rejected boundary pair, through the general composition theorem. -/
theorem two_flips_reject : ¬ behavior (compose flip flip) false true := by
  rw [two_flips]
  decide

def swapBool : Bool ≃ Bool :=
  ⟨Bool.not, Bool.not, by intro b; cases b <;> rfl, by intro b; cases b <;> rfl⟩

/-- Renaming the two internal choices is exact even when one is constrained. -/
theorem renamed_one (a b : Unit) :
    behavior (renameInternal one swapBool) a b ↔ behavior one a b :=
  behavior_renameInternal one swapBool a b

/-- Inconsistency cannot be repaired by adding unconstrained downstream choices. -/
theorem inconsistent_then_two : ¬ behavior (compose inconsistent two) () () := by
  rw [behavior_compose]
  rintro ⟨b, hn, _⟩
  exact inconsistent_empty () b hn

/-- Boundary permutations act on both ends, preserving the flip specification. -/
theorem renamed_flip (a b : Bool) :
    behavior (renameBoundary flip swapBool swapBool) a b ↔ b = !a := by
  rw [behavior_renameBoundary, flip_behavior]
  cases a <;> cases b <;> decide

theorem identity_then_flip (a b : Bool) :
    behavior (compose (wire Bool) flip) a b ↔ b = !a := by
  rw [behavior_wire_left, flip_behavior]

/-- Hidden ambiguity remains in the composite even when its boundary is fixed. -/
theorem two_then_wire_ambiguous : ambiguous (compose two (wire Unit)) () () := by
  refine ⟨(false, (), PUnit.unit), (true, (), PUnit.unit), ?_, ?_, ?_⟩
  · exact ⟨trivial, rfl⟩
  · exact ⟨trivial, rfl⟩
  · intro h
    exact Bool.false_ne_true (congrArg Prod.fst h)

end Examples.OpenConstraint
