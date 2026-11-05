import SquareKit.Internal.DependentJudgments.MemoNormalization
import SquareKit.Internal.DependentJudgments.NativeDerivedComparisons

/-! A generated memo specialization with unequal dependent Type presentations.
The certificate remains value-dependent; native identity is a truncated instance. -/
namespace Examples.GuardedNativeMemo
open SquareKit.GuardedTheory
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open SquareKit.Internal.DependentJudgments.CoherentTypePresentations
open SquareKit.Internal.PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false

abbrev gamma : Contextual.Expression (Fin 5) := .var 0
abbrev alpha : Contextual.Expression (Fin 5) := .var 1
abbrev beta : Contextual.Expression (Fin 5) := .var 2
abbrev point : Contextual.Expression (Fin 5) := .var 3
abbrev input : Contextual.Expression (Fin 5) := .var 4
abbrev premises : List (Contextual.Judgment (Fin 5)) :=
  [term gamma alpha point, family (extend gamma alpha) beta,
    term gamma (subTy beta (sectionSub gamma alpha point)) input]

def point_typed : Tm (Ω := premises) gamma alpha point := .hypothesis (by simp [premises])
def family_typed : Ty (Ω := premises) (extend gamma alpha) beta := .hypothesis (by simp [premises])
def input_typed : Tm (Ω := premises) gamma (subTy beta (sectionSub gamma alpha point)) input :=
  .hypothesis (by simp [premises])

def parameters : Memo.Parameters premises where
  Γ := gamma
  A := alpha
  B := beta
  x := point
  y := point
  z := point
  q := Contextual.reflexivity alpha point
  u := input
  x_typed := point_typed
  y_typed := point_typed
  z_typed := point_typed
  B_typed := family_typed
  q_typed := point_typed.reflexivity
  u_typed := input_typed

abbrev loop := Contextual.reflexivity alpha point
abbrev directValue := Contextual.transport gamma alpha beta point point loop
  (Contextual.transport gamma alpha beta point point loop input)
abbrev directCertificate := Contextual.eta gamma alpha beta point point point loop loop input

def directValue_typed : Tm (Ω := premises) gamma (subTy beta (sectionSub gamma alpha point)) directValue :=
  Tm.transport family_typed point_typed point_typed point_typed.reflexivity
    (Tm.transport family_typed point_typed point_typed point_typed.reflexivity input_typed)

def directCertificate_typed : Tm (Ω := premises) gamma
    (Contextual.identity (subTy beta (sectionSub gamma alpha point)) directValue
      (Contextual.transport gamma alpha beta point point
        (Contextual.concat gamma alpha point point point loop loop) input)) directCertificate :=
  Tm.eta family_typed point_typed point_typed point_typed.reflexivity input_typed
    point_typed point_typed.reflexivity

def dependentAction_typed := parameters.dependentAction_typed
  point_typed.reflexivity point_typed.reflexivity point_typed.reflexivity.reflexivity

universe u
variable (M : SquareKit.Internal.PathTransport.Typed.Model.{u})
variable (Γ : M.Context) (A : M.Family Γ) (B : M.Family (M.extend Γ A))
variable (x : M.Section Γ A) (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A x)))

def environment : Fin 5 → Value M.toStructuralModel :=
  ![.context Γ, .family Γ A, .family (M.extend Γ A) B, .term Γ A x,
    .term Γ (M.subTy B (M.toStructuralModel.sectionSub A x)) b]

theorem inputs : ∀ a ∈ premises, a.eval (Contextual.algebra M) (environment M Γ A B x b) := by
  have hs := sectionSub_eval M (environment M Γ A B x b) gamma alpha point Γ A x rfl rfl rfl
  intro a ha
  simp only [premises, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact ⟨Γ, A, x, rfl, rfl, rfl⟩
  · refine ⟨M.extend Γ A, B, ?_, rfl⟩
    simp [gamma, alpha, Term.eval, Contextual.algebra, SquareKit.Internal.DependentJudgments.operation, environment]
  · refine ⟨Γ, M.subTy B (M.toStructuralModel.sectionSub A x), b, rfl, ?_, rfl⟩
    change SquareKit.Internal.DependentJudgments.operation M.toStructuralModel .subTy
      ![.family (M.extend Γ A) B,
        (sectionSub gamma alpha point).eval (Contextual.algebra M) (environment M Γ A B x b)] = _
    rw [hs]
    simp [SquareKit.Internal.DependentJudgments.operation]

theorem directValue_eval : directValue.eval (Contextual.algebra M) (environment M Γ A B x b) =
    .term Γ (M.subTy B (M.toStructuralModel.sectionSub A x)) b := by
  have hp : loop.eval (Contextual.algebra M) (environment M Γ A B x b) =
      .term Γ (M.identity A x x) (M.reflexivity A x) := by
    simp [loop, alpha, point, Term.eval, Contextual.algebra, Contextual.operation, environment]
  have h₁ := transport_eval M (environment M Γ A B x b) gamma alpha beta point point loop input
    Γ A B x x (M.reflexivity A x) b rfl rfl rfl rfl rfl hp rfl
  rw [transportValue_refl] at h₁
  have h₂ := transport_eval M (environment M Γ A B x b) gamma alpha beta point point loop
    (Contextual.transport gamma alpha beta point point loop input)
    Γ A B x x (M.reflexivity A x) b rfl rfl rfl rfl rfl hp h₁
  simpa only [transportValue_refl] using h₂

def semanticCertificateType := M.identity (M.subTy B (M.toStructuralModel.sectionSub A x))
  (transportValue M A B x x (M.reflexivity A x) (transportValue M A B x x (M.reflexivity A x) b))
  (transportValue M A B x x (concatValue M A x x x (M.reflexivity A x) (M.reflexivity A x)) b)

theorem directCertificate_eval :
    directCertificate.eval (Contextual.algebra M) (environment M Γ A B x b) =
      .term Γ (semanticCertificateType M Γ A B x b)
        (etaValue M A B x x x (M.reflexivity A x) (M.reflexivity A x) b) := by
  have hp : loop.eval (Contextual.algebra M) (environment M Γ A B x b) =
      .term Γ (M.identity A x x) (M.reflexivity A x) := by
    simp [loop, alpha, point, Term.eval, Contextual.algebra, Contextual.operation, environment]
  exact eta_eval M (environment M Γ A B x b) gamma alpha beta point point point loop loop input
    Γ A B x x x (M.reflexivity A x) (M.reflexivity A x) b rfl rfl rfl rfl rfl rfl hp hp rfl

/-- The selected contextual package is interpreted through its generated
normalization, retaining the exact chosen certificate. -/
theorem selectedValue_eval :
    (parameters.value loop).eval (Contextual.algebra M) (environment M Γ A B x b) =
      .term Γ (M.subTy B (M.toStructuralModel.sectionSub A x)) b := by
  have he := Contextual.interpret (parameters.value_atPath point_typed.reflexivity)
    M (environment M Γ A B x b) (inputs M Γ A B x b)
  exact he.trans (directValue_eval M Γ A B x b)

theorem selectedCertificate_eval :
    (parameters.certificate loop).eval (Contextual.algebra M) (environment M Γ A B x b) =
      .term Γ (semanticCertificateType M Γ A B x b)
        (etaValue M A B x x x (M.reflexivity A x) (M.reflexivity A x) b) := by
  have he := Contextual.interpret (parameters.certificate_atPath point_typed.reflexivity)
    M (environment M Γ A B x b) (inputs M Γ A B x b)
  exact he.trans (directCertificate_eval M Γ A B x b)

namespace FinitePresentation
open NativeDerivedComparisons
local notation "M₀" => NativeType.model Nat (fun n => Fin (n + 1))
local notation "S₀" => NativeType.structuralModel Nat (fun n => Fin (n + 1))

def dependentFamily (z : Sigma FiniteOption.direct) : Type := Fin (z.2.val + 1)
def codedDependentFamily (z : Sigma FiniteOption.coded) : Type :=
  Option (Fin ((finSuccEquiv z.1.1).symm z.2).val)
def comparison : FamilyComparison FiniteOption.comparison.total dependentFamily codedDependentFamily := by
  intro z
  change Fin (z.2.val + 1) ≃ Option (Fin ((finSuccEquiv z.1.1).symm (finSuccEquiv z.1.1 z.2)).val)
  simpa only [Equiv.symm_apply_apply] using finSuccEquiv z.2.val

def selected (γ : FiniteOption.Base) : FiniteOption.direct γ := ⟨γ.1, Nat.lt_succ_self _⟩
def selectedValue (γ : FiniteOption.Base) : dependentFamily ⟨γ, selected γ⟩ := ⟨γ.1, Nat.lt_succ_self _⟩
def codedPoint := FiniteOption.comparison.term selected
def codedValue := (atSection FiniteOption.comparison comparison selected).term selectedValue

def sourceInput : (M₀).Section FiniteOption.Base
    ((M₀).subTy dependentFamily ((M₀).toStructuralModel.sectionSub FiniteOption.direct ⟨selected⟩)) := by
  change ULift ((γ : FiniteOption.Base) → dependentFamily ⟨γ, selected γ⟩)
  exact ⟨selectedValue⟩
def targetInput : (M₀).Section FiniteOption.Base
    ((M₀).subTy codedDependentFamily ((M₀).toStructuralModel.sectionSub FiniteOption.coded ⟨codedPoint⟩)) := by
  change ULift ((γ : FiniteOption.Base) → codedDependentFamily ⟨γ, codedPoint γ⟩)
  exact ⟨codedValue⟩

def sourceEnvironment := environment M₀ FiniteOption.Base FiniteOption.direct dependentFamily ⟨selected⟩ sourceInput
def targetEnvironment := environment M₀ FiniteOption.Base FiniteOption.coded codedDependentFamily ⟨codedPoint⟩ targetInput

theorem source_inputs : ∀ a ∈ premises, a.eval (Contextual.algebra M₀) sourceEnvironment :=
  inputs M₀ FiniteOption.Base FiniteOption.direct dependentFamily ⟨selected⟩ sourceInput
theorem target_inputs : ∀ a ∈ premises, a.eval (Contextual.algebra M₀) targetEnvironment :=
  inputs M₀ FiniteOption.Base FiniteOption.coded codedDependentFamily ⟨codedPoint⟩ targetInput

def certificateComparison : FamilyComparison FiniteOption.flip
    (semanticCertificateType M₀ FiniteOption.Base FiniteOption.direct dependentFamily ⟨selected⟩ sourceInput)
    (semanticCertificateType M₀ FiniteOption.Base FiniteOption.coded codedDependentFamily ⟨codedPoint⟩ targetInput) :=
  etaFamily FiniteOption.comparison comparison selected selected selected
    ((M₀).reflexivity FiniteOption.direct ⟨selected⟩)
    ((M₀).reflexivity FiniteOption.direct ⟨selected⟩) sourceInput

theorem source_certificate_comparison :
    Option.map (fun t => certificateComparison.term t.down)
      ((directCertificate.eval (Contextual.algebra M₀) sourceEnvironment).termAt FiniteOption.Base
        (semanticCertificateType M₀ FiniteOption.Base FiniteOption.direct dependentFamily ⟨selected⟩ sourceInput)) =
    Option.map (fun t => t.down)
      ((directCertificate.eval (Contextual.algebra M₀) targetEnvironment).termAt FiniteOption.Base
        (semanticCertificateType M₀ FiniteOption.Base FiniteOption.coded codedDependentFamily ⟨codedPoint⟩ targetInput)) := by
  unfold sourceEnvironment targetEnvironment
  rw [directCertificate_eval, directCertificate_eval]
  simp only [Value.termAt_term, Option.map_some]
  exact congrArg some (eta_compare FiniteOption.comparison comparison selected selected selected
    ((M₀).reflexivity FiniteOption.direct ⟨selected⟩)
    ((M₀).reflexivity FiniteOption.direct ⟨selected⟩) sourceInput)

theorem source_selected_three :
    Option.map (fun t => (t.down (3, false)).val)
      ((directValue.eval (Contextual.algebra M₀) sourceEnvironment).termAt FiniteOption.Base
        ((S₀).subTy dependentFamily ((S₀).sectionSub FiniteOption.direct ⟨selected⟩))) = some 3 := by
  unfold sourceEnvironment
  erw [directValue_eval]
  simp only [NativeType.model, Value.termAt_term, Option.map_some]
  rfl

theorem target_selected_some_two :
    Option.map (fun t => t.down (FiniteOption.flip (3, false)))
      ((directValue.eval (Contextual.algebra M₀) targetEnvironment).termAt FiniteOption.Base
        ((S₀).subTy codedDependentFamily ((S₀).sectionSub FiniteOption.coded ⟨codedPoint⟩))) =
      some (some (⟨2, by decide⟩ : Fin 3)) := by
  unfold targetEnvironment
  erw [directValue_eval]
  simp only [NativeType.model, Value.termAt_term, Option.map_some]
  have h := (atSection FiniteOption.comparison comparison selected).term_apply selectedValue (3, false)
  change some (codedValue (FiniteOption.flip (3, false))) = _
  rw [show codedValue (FiniteOption.flip (3, false)) = _ from h]
  rfl

/-- The same selected source certificate, including the normalization from
its varying section, is compared in the two unequal dependent presentations. -/
theorem selected_certificate_comparison :
    Option.map (fun t => certificateComparison.term t.down)
      (((parameters.certificate loop).eval (Contextual.algebra M₀) sourceEnvironment).termAt FiniteOption.Base
        (semanticCertificateType M₀ FiniteOption.Base FiniteOption.direct dependentFamily ⟨selected⟩ sourceInput)) =
    Option.map (fun t => t.down)
      (((parameters.certificate loop).eval (Contextual.algebra M₀) targetEnvironment).termAt FiniteOption.Base
        (semanticCertificateType M₀ FiniteOption.Base FiniteOption.coded codedDependentFamily ⟨codedPoint⟩ targetInput)) := by
  unfold sourceEnvironment targetEnvironment
  rw [selectedCertificate_eval, selectedCertificate_eval]
  simp only [Value.termAt_term, Option.map_some]
  exact congrArg some (eta_compare FiniteOption.comparison comparison selected selected selected
    ((M₀).reflexivity FiniteOption.direct ⟨selected⟩)
    ((M₀).reflexivity FiniteOption.direct ⟨selected⟩) sourceInput)

/-- A concrete application of the constructed varying-certificate and apd
comparison, with both displayed dependent families changed. -/
def etaPresentations := etaPresentation (Base := Nat) (Fiber := fun n => Fin (n + 1)) FiniteOption.comparison comparison selected selected selected
  ((M₀).reflexivity FiniteOption.direct ⟨selected⟩) sourceInput

theorem selected_dependent_action_comparison
    (p p' : (γ : FiniteOption.Base) → PathFamily selected selected γ)
    (h : (S₀).Section FiniteOption.Base ((S₀).identity (PathFamily selected selected) ⟨p⟩ ⟨p'⟩)) :
    etaPresentations.DependentActionCompared FiniteOption.comparison selected selected p p' h :=
  apdEta_compare FiniteOption.comparison comparison selected selected selected
    ((M₀).reflexivity FiniteOption.direct ⟨selected⟩) sourceInput p p' h

end FinitePresentation
end Examples.GuardedNativeMemo
