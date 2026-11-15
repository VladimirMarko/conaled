import SquareKit.Internal.DependentJudgments.Sigma.Theory
import SquareKit.Internal.DependentJudgments.Sigma.Native

/-! Syntax boundaries and semantic admission reject different mistakes. A
well-formed type equality still needs semantic evidence in the chosen model. -/
namespace SquareKit.Internal.DependentJudgments.Sigma
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false

/-- Both endpoints are types under the ordinary formation premises. -/
abbrev collapseRule := formationSchema (.eq (sigma (.var 1) (.var 2)) (.var 1))

private abbrev counterModel := NativeType.model Unit (fun _ => Unit)
private abbrev counterCapability := Native.capability Unit (fun _ => Unit)
private def collapseEnvironment : Fin 3 → Value counterModel.toStructuralModel :=
  ![.context Unit, .family Unit (fun _ => Unit),
    .family ((_ : Unit) × Unit) (fun _ => Bool)]

/-- Even an equivalence cannot identify this dependent sum with its first type. -/
theorem no_collapse_equivalence : ¬ Nonempty (((_ : Unit) × Bool) ≃ Unit) := by
  rintro ⟨e⟩
  have h : e ⟨(), false⟩ = e ⟨(), true⟩ := Subsingleton.elim _ _
  have h' := congrArg (fun p : (_ : Unit) × Bool => p.2) (e.injective h)
  cases h'

/-- The endpoints of the rejected equation are valid in the same environment. -/
theorem collapse_boundary :
    (family (.var 0) (sigma (.var 1) (.var 2))).eval (algebra counterModel counterCapability) collapseEnvironment ∧
    (family (.var 0) (.var 1)).eval (algebra counterModel counterCapability) collapseEnvironment := by
  constructor
  · refine ⟨Unit, fun _ => (_ : Unit) × Bool, rfl, ?_⟩
    simp [Term.eval, algebra, operation, collapseEnvironment, Native.capability, inputs, Value.familyAt, counterModel, NativeType.model, NativeType.structuralModel]
  · exact ⟨Unit, fun _ => Unit, rfl, rfl⟩

/-- Syntactically well-formed equations are not automatically admitted. -/
theorem collapse_rejected : ¬ Satisfies (algebra counterModel counterCapability) collapseRule := by
  intro valid
  have h := valid collapseEnvironment (by
    intro i
    fin_cases i
    · exact ⟨Unit, fun _ => Unit, rfl, rfl⟩
    · refine ⟨((_ : Unit) × Unit), fun _ => Bool, ?_, rfl⟩
      simp [Term.eval, algebra, Contextual.algebra, DependentJudgments.operation, collapseEnvironment, counterModel, NativeType.model, NativeType.structuralModel])
  change (sigma (.var 1) (.var 2)).eval (algebra counterModel counterCapability) collapseEnvironment =
    collapseEnvironment 1 at h
  simp only [Term.eval, FinitaryTerm.fold, algebra, operation, collapseEnvironment,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h
  simp [inputs, Value.familyAt, counterModel, NativeType.model, NativeType.structuralModel] at h
  have he : ((_ : Unit) × Bool) = Unit := congrFun h ()
  exact no_collapse_equivalence ⟨Equiv.cast he⟩

/-- Omitting the second-family guard is a separate, malformed admission attempt. -/
abbrev missingDependencyRule : Rule signature where
  parameterCount := 3
  hypotheses := 1
  premise := ![family (.var 0) (.var 1)]
  conclusion := family (.var 0) (sigma (.var 1) (.var 2))

theorem missing_dependency_rejected :
    ¬ Satisfies (algebra counterModel counterCapability) missingDependencyRule := by
  intro valid
  let ρ : Fin 3 → Value counterModel.toStructuralModel :=
    ![.context Unit, .family Unit (fun _ => Unit), .invalid]
  have h := valid ρ (by intro i; fin_cases i; exact ⟨Unit, fun _ => Unit, rfl, rfl⟩)
  rcases h with ⟨Γ, A, _, hA⟩
  change (sigma (.var 1) (.var 2)).eval (algebra counterModel counterCapability) ρ = .family Γ A at hA
  simp [Term.eval, algebra, operation, inputs, ρ, Value.familyAt] at hA

end SquareKit.Internal.DependentJudgments.Sigma
