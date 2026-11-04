import Examples.IndexedCompositional
import Examples.EquationTranspose
import Applications.Languages.EquationComposition

/-! Checked presentation changes, mixed finite terms, and the local-rule boundary. -/
namespace Examples.EquationComposition
open SquareKit.IndexedCompositional
open SquareKit.EquationComposition

namespace Vectors
open IndexedCompositionalExamples.Vectors

def rows := SquareKit.EquationTranspose.transpose equations

theorem rows_rule : compileRows rows primitiveMeaning = rule := compile_transpose _ _

/-- Existing constructor-source equations agree on the shared head observation. -/
theorem original_cons_head (n a : Nat) (xs : Vec n) :
    rule.out (.cons n a) (fun _ => (native n xs).1) =
      Examples.EquationTranspose.Vectors.equations.observe
        Examples.EquationTranspose.Vectors.meaning (i := n+1) .at ⟨.cons n,(a,xs)⟩ ⟨0, Nat.zero_lt_succ n⟩ := rfl

/-- This cell returns the original tail, not its successor, at exactly length n. -/
theorem cons_retained (n a : Nat) (xs : SquareKit.EquationComposition.Outputs signature behavior (.cons n a)) :
    (compileRows rows primitiveMeaning).step (.cons n a) xs () = .leaf (.ret 0) := by
  rw [rows_rule]; rfl

/-- The public all-term bridge is exercised by cons, double, and nil together. -/
example : behavior.observe ((compileRows rows primitiveMeaning).lift native)
    (.step () .stop) (double (cons 7 (cons 11 nil))) = 22 := by
  erw [← observations equations primitiveMeaning algebra native compatible native
    (fun _ x => x) ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩]
  rfl

/-- The source lookup primitive can inspect a second coordinate. Current child
outputs expose only the head, so no local output function can represent it. -/
theorem second_coordinate_not_local :
    ¬ ∃ f : Nat → Nat, ∀ v : Vec 2, v 1 = f ((native 2 v).1) := by
  rintro ⟨f,h⟩
  have h0 := h (fun _ => 0)
  have h1 := h (Fin.cases 0 (fun _ => 1))
  change 0 = f 0 at h0
  change 1 = f 0 at h1
  have bad : (0 : Nat) = 1 := h0.trans h1.symm
  cases bad
end Vectors

namespace Parsing
open LanguageWitnesses
open LanguageWitnesses.EquationComposition

def rows := SquareKit.EquationTranspose.transpose (equations (α := Bool))

theorem rows_rule : compileRows rows meaning = rule := compile_transpose _ _

/-- Two successful branches deliberately carry different scalar witnesses. -/
def mixed : Term signature Source
    (fun w => (Nat × atom true w) ⊕ (Nat × atom true w), 1) :=
  .node (.union _ _ 1) (fun k => Fin.cases
    (.node (.scale (atom true) 1 (.yes 7)) (fun _ => .leaf (.atom true)))
    (fun _ => .node (.scale (atom true) 1 (.yes 11)) (fun _ => .leaf (.atom true))) k)

example : (Term.fold targetAlgebra LanguageWitnesses.IndexedCompositional.unfold mixed).lookup
    [true] (by decide) = Decision.yes (.inl (7, ⟨rfl⟩)) := by
  rw [recovered]
  rfl

/-- Row presentation preserves the same branch and scalar after the request. -/
example : behavior.observe ((compileRows rows meaning).lift LanguageWitnesses.IndexedCompositional.source)
    (.step true .stop) mixed = Decision.yes (.inl (7, ⟨rfl⟩)) := by
  erw [← observations equations meaning sourceAlgebra LanguageWitnesses.IndexedCompositional.source
    sourceCompatible LanguageWitnesses.IndexedCompositional.source (fun _ x => x)
    ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩]
  rfl
end Parsing
end Examples.EquationComposition
