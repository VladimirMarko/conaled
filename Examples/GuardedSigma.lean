import SquareKit.Internal.DependentJudgments.Sigma.Authoring
import SquareKit.Internal.DependentJudgments.Sigma.Native
import SquareKit.Internal.DependentJudgments.Sigma.Rejection
import SquareKit.Internal.DependentJudgments.Sigma.Recovery
import SquareKit.Internal.DependentJudgments.Sigma.Composition

/-! Checked clients of constructor admission. The source derivations precede
selection of a model; concrete observations retain the varying fiber and motive. -/
namespace Examples.GuardedSigma
open SquareKit SquareKit.Internal SquareKit.Internal.DependentJudgments
open SquareKit.GuardedTheory
set_option backward.isDefEq.respectTransparency false

private abbrev M := NativeType.model Unit (fun _ => Unit)
private abbrev cap := Sigma.Native.capability Unit (fun _ => Unit)
private abbrev A : M.Family Unit := fun _ => Nat
private abbrev B : M.Family (M.extend Unit A) := fun p => Fin (p.2 + 1)
private abbrev C : M.Family (M.extend Unit (cap.sigma A B)) := fun p => Fin (p.2.1 + 1)
private def branch : M.Section (M.extend (M.extend Unit A) B) (M.subTy C (cap.pack A B)) :=
  ⟨fun p => p.2⟩
private def ρ : Fin 5 → Value M.toStructuralModel :=
  ![.context Unit, .family Unit A, .family (M.extend Unit A) B,
    .family (M.extend Unit (cap.sigma A B)) C,
    .term (M.extend (M.extend Unit A) B) (M.subTy C (cap.pack A B)) branch]

/-- The model-specific work supplies only the four stated source assumptions. -/
theorem branch_assumptions : ∀ p ∈ List.ofFn Sigma.splitRule.premise, p.eval (Sigma.algebra M cap) ρ := by
  intro p hp
  rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
  change Fin 4 at i
  fin_cases i
  · exact ⟨Unit, A, rfl, rfl⟩
  · refine ⟨M.extend Unit A, B, ?_, rfl⟩
    simp [Term.eval, Sigma.algebra, Contextual.algebra, operation, ρ]
  · refine ⟨M.extend Unit (cap.sigma A B), C, ?_, rfl⟩
    simp [Term.eval, Sigma.algebra, Sigma.operation, Contextual.algebra, operation, ρ]
  · refine ⟨M.extend (M.extend Unit A) B, M.subTy C (cap.pack A B), branch, ?_, ?_, rfl⟩ <;>
      simp [Term.eval, Sigma.algebra, Sigma.operation, Contextual.algebra, operation, ρ]

/-- An ordinary author reuses the generic interpretation theorem. -/
theorem dependent_elimination_admitted :
    Sigma.splitRule.conclusion.eval (Sigma.algebra M cap) ρ :=
  Sigma.interpret Sigma.splitDerivation M cap ρ branch_assumptions

/-- The branch computes in Fin(n+1), including the smallest fiber. -/
example (n : Nat) (i : Fin (n + 1)) :
    (cap.split A B C branch).down ⟨(), n, i⟩ = i :=
  Sigma.Native.bounded_split n i

example : (cap.split A B C branch).down ⟨(), 0, 0⟩ = 0 :=
  Sigma.Native.bounded_split 0 0

/-- Both pair introduction and split use the same varying second family. -/
example (n : Nat) (i : Fin (n + 1)) :
    (cap.pair A B ⟨fun _ => n⟩ ⟨fun _ => i⟩).down () = ⟨n, i⟩ := rfl

/-- Generic beta at an introduced object pair, with the dependent result type retained. -/
example (n : Nat) (i : Fin (n + 1)) :
    HEq (M.subTm (cap.split A B C branch)
      (M.toStructuralModel.sectionSub (cap.sigma A B) (cap.pair A B ⟨fun _ => n⟩ ⟨fun _ => i⟩)))
      (M.subTm branch (M.pairSub B (M.toStructuralModel.sectionSub A ⟨fun _ => n⟩) ⟨fun _ => i⟩)) :=
  cap.split_pair A B _ _ C branch

/-- The false type equation is rejected despite well-formed endpoints. -/
example : ¬ Nonempty (((_ : Unit) × Bool) ≃ Unit) := Sigma.no_collapse_equivalence


/-- An exact selected output follows from the source computation derivation and
its interpretation, with no constructor coherence supplied by this client. -/
theorem source_beta_selected (n : Nat) (i : Fin (n + 1)) :
    (((Sigma.subTm (Sigma.split (.var 1) (.var 2) (.var 4)) (Sigma.pack (.var 1) (.var 2))).eval
      (Sigma.algebra M cap) ρ).termAt (M.extend (M.extend Unit A) B) (M.subTy C (cap.pack A B))).map
        (fun t => t.down ⟨⟨(), n⟩, i⟩) = some i := by
  have h := Sigma.interpret Sigma.splitBetaDerivation M cap ρ branch_assumptions
  change (Sigma.subTm (Sigma.split (.var 1) (.var 2) (.var 4)) (Sigma.pack (.var 1) (.var 2))).eval
    (Sigma.algebra M cap) ρ = ρ 4 at h
  rw [h]
  simp [ρ, branch]

end Examples.GuardedSigma
