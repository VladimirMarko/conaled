import SquareKit.Internal.GraphTargetComparison

/-! Checked native observations of K, independent of installed expression emission.
The arithmetic calculation fixes the order: increment 2 to 3, then double to 6.
-/
namespace Examples.GraphTarget
open SquareKit.Internal

/-- The existential binder is y, followed by x and z, even with equal carriers. -/
theorem binder_order (x y z : Nat) :
    (SquareKit.Internal.GraphTarget.translateFormula (Graph.body .first .second)).eval
      (Graph.model (fun n : Nat => n + 1) (fun n => 2 * n))
      (Env.extend y (Graph.environment (fun n : Nat => n + 1) (fun n => 2 * n) x z)) ↔
      y = x + 1 ∧ z = 2 * y := Iff.rfl

theorem concrete_forward :
    (∃ y : Nat, y = 3 ∧ 6 = 2 * y) → (6 : Nat) = 2 * (2 + 1) :=
  (SquareKit.Internal.GraphTarget.graph_equivalence (fun n : Nat => n + 1) (fun n => 2 * n) 2 6).mp

theorem concrete_reverse : ∃ y : Nat, y = 3 ∧ 6 = 2 * y :=
  (SquareKit.Internal.GraphTarget.graph_equivalence (fun n : Nat => n + 1) (fun n => 2 * n) 2 6).mpr rfl

/-- Swapping the arrows is type-correct for Nat but produces 5 instead of 6. -/
theorem wrong_order_rejected : ¬ (∃ y : Nat, y = 3 ∧ 5 = 2 * y) := by
  intro h
  have bad := (SquareKit.Internal.GraphTarget.graph_equivalence (fun n : Nat => n + 1) (fun n => 2 * n) 2 5).mp h
  exact (by decide : (5 : Nat) ≠ 6) bad

/-- Three different carriers, with an explicit witness and both directions. -/
theorem distinct_carriers :
    (∃ y : Bool, y = true ∧ () = (fun _ : Bool => ()) y) ↔ (() : Unit) = () :=
  SquareKit.Internal.GraphTarget.graph_equivalence (fun _ : Nat => true) (fun _ : Bool => ()) 2 ()

example : ∃ y : Bool, y = true ∧ () = (fun _ : Bool => ()) y :=
  distinct_carriers.mpr rfl

/-- No inhabited-carrier assumption is smuggled into universal closure. -/
theorem empty_input (x : Empty) (z : Nat) :
    (∃ y : Empty, y = x ∧ z = Empty.elim y) ↔ z = Empty.elim x :=
  SquareKit.Internal.GraphTarget.graph_equivalence (fun x : Empty => x) (fun y : Empty => Empty.elim y) x z

/-- With inhabited input and output an empty middle admits no first arrow. -/
theorem empty_middle_obstruction (f : Unit → Empty) : False := Empty.elim (f ())

example : SquareKit.Internal.GraphTarget.Declaration.denote.{0} SquareKit.Internal.GraphTarget.forwardDeclaration :=
  SquareKit.Internal.GraphTarget.declaration_sound SquareKit.Internal.GraphTarget.forwardDeclaration

example : SquareKit.Internal.GraphTarget.Declaration.denote.{1} SquareKit.Internal.GraphTarget.backwardDeclaration :=
  SquareKit.Internal.GraphTarget.declaration_sound SquareKit.Internal.GraphTarget.backwardDeclaration

/-- Conversion compares proofs while preserving the same formula observation. -/
example (h : (∃ y : Nat, y = 3 ∧ 6 = 2 * y)) :
    SquareKit.Internal.GraphTarget.sound (Graph.model (fun n : Nat => n + 1) (fun n => 2 * n))
      (.cut SquareKit.Internal.GraphTarget.forward .ident)
      (Graph.environment (fun n : Nat => n + 1) (fun n => 2 * n) 2 6) h =
    SquareKit.Internal.GraphTarget.sound (Graph.model (fun n : Nat => n + 1) (fun n => 2 * n)) SquareKit.Internal.GraphTarget.forward
      (Graph.environment (fun n : Nat => n + 1) (fun n => 2 * n) 2 6) h :=
  SquareKit.Internal.GraphTarget.proof_irrel
    (Graph.model (fun n : Nat => n + 1) (fun n => 2 * n))
    (.cut SquareKit.Internal.GraphTarget.forward .ident) SquareKit.Internal.GraphTarget.forward
    (Graph.environment (fun n : Nat => n + 1) (fun n => 2 * n) 2 6) h

end Examples.GraphTarget
