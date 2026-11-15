import Examples.DependentAuthorBaseline
import Examples.DependentAuthorCandidate
import Examples.DependentAuthorBaselineReference
import Examples.DependentAuthorCandidateReference
import SquareKit.Internal.DependentJudgments.Sigma.Native

/-! Private reference specializations for the dependent author trial. These
cases establish inhabited inputs and retain selected J data; they are excluded
from both public author handoffs. Post-trial cases also consume the exact author
submissions imported above. Those modules are experimental, unmodified evidence
artifacts; their missing headers are preserved to keep the measured bytes exact.
Scope and unresolved questions: docs/research/dependent-author-interface-trial.md.
Native equality remains lower-truncated. -/
namespace Examples.DependentAuthorTrialCases
open SquareKit.Internal SquareKit.Internal.PathTransport Typed Authoring
open SquareKit.Internal.DependentJudgments SquareKit.GuardedTheory
set_option backward.isDefEq.respectTransparency false

abbrev native := NativeType.model Nat (fun n => Fin (n + 1))
abbrev stable := Sigma.Native.stable Nat (fun n => Fin (n + 1))

namespace Baseline
open NamedCaller

def command := DependentAuthorReference.Baseline.certificateCommand
  earlier base x.deriv generalized qAtBType qAtB
def certificate := DependentAuthorReference.Baseline.certificate
  earlier base x.deriv generalized qAtBType qAtB
def first := DependentAuthorReference.Baseline.firstWeakening
  earlier base x.deriv generalized qAtBType qAtB
def second := DependentAuthorReference.Baseline.secondWeakening
  earlier base x.deriv generalized qAtBType qAtB
def comparison := DependentAuthorReference.Baseline.dependentWeakeningComparison
  earlier base x.deriv generalized qAtBType qAtB
def aligned := DependentAuthorReference.Baseline.certificateAligned
  earlier base x.deriv generalized qAtBType qAtB first second
def composite := TmDeriv.sub certificate (SubDeriv.comp first second)
def twice := DependentAuthorReference.Baseline.dependentWeakeningCertificate
  earlier base x.deriv generalized qAtBType qAtB

/-- The selected semantic section carried by a source derivation's index. -/
private def selectedCode {Γ : RawCtx} {γ : CtxCode.{1}} {A t : Expr} {a : TyCode γ}
    {ξ : TmCode γ a} (_h : TmDeriv Γ γ A a t ξ) : native.Section (γ native) (a native) :=
  ξ native

/-- Specialize the reference's exact selected-certificate validity at the
inhabited native model and the named dependent three-binder caller. -/
theorem certificate_valid : interpretTm native twice = selectedCode twice :=
  DependentAuthorReference.Baseline.certificateValidity
    earlier base x.deriv generalized qAtBType qAtB first second native

theorem extension_selected : interpretTm native twice = selectedCode twice :=
  DependentAuthorReference.Baseline.extensionSelected
    earlier base x.deriv generalized qAtBType qAtB first second native stable

/-- The full named three-binder tail supports the reference's dependent
weakening comparison, including the conversion to its composite result type. -/
theorem comparison_sound : interpretTm native aligned = interpretTm native composite := by
  rw [interpretTm_agrees, interpretTm_agrees]
  exact congrFun (termSound comparison) native

/-- The accepted baseline submission reuses its generic result at the actual
three-binder tail and two certificate-dependent weakenings. -/
theorem author_certificate_valid :
    interpretTm native DependentAuthorTrial.Baseline.workedDependentWeakening =
      selectedCode DependentAuthorTrial.Baseline.workedDependentWeakening :=
  DependentAuthorTrial.Baseline.certificateValidity
    earlier base x.deriv generalized qAtBType qAtB
    (DependentAuthorTrial.Baseline.firstWeakening earlier base x.deriv generalized qAtBType qAtB)
    (DependentAuthorTrial.Baseline.secondWeakening earlier base x.deriv generalized qAtBType qAtB)
    native

/-- The exact author comparison specializes to an inhabited full stable model. -/
theorem author_comparison_sound :
    interpretTm native
      (DependentAuthorTrial.Baseline.certificateAligned earlier base x.deriv generalized qAtBType qAtB
        (DependentAuthorTrial.Baseline.firstWeakening earlier base x.deriv generalized qAtBType qAtB)
        (DependentAuthorTrial.Baseline.secondWeakening earlier base x.deriv generalized qAtBType qAtB)) =
    interpretTm native
      (DependentAuthorTrial.Baseline.certificateComposite earlier base x.deriv generalized qAtBType qAtB
        (DependentAuthorTrial.Baseline.firstWeakening earlier base x.deriv generalized qAtBType qAtB)
        (DependentAuthorTrial.Baseline.secondWeakening earlier base x.deriv generalized qAtBType qAtB)) :=
  DependentAuthorTrial.Baseline.interpretedCertificateComparison
    earlier base x.deriv generalized qAtBType qAtB _ _ native

end Baseline

/-- Evaluate the concrete caller's annotations without assuming any source
judgment in the candidate. The candidate hypotheses are checked below. -/
structure Inputs where
  context : native.Context
  family : native.Family context
  point : native.Section context family
  length : Nat
  tail : StructuralModel.Telescope native.toStructuralModel
    (native.toStructuralModel.pathContext family point) length
  valueFamily : native.Family tail.total
  value : native.Section tail.total valueFamily

private def inputsOf {Γ : RawCtx} {γ : CtxCode.{1}} {A x : Expr} {a : TyCode γ}
    {ξ : TmCode γ a} {n : Nat} {Ξ : RawCtx} {T : TelCode (pathCode a ξ) n}
    {Q p : Expr} {q : TyCode (telTotal T)} {π : TmCode (telTotal T) q}
    (_hΓ : CtxDeriv Γ γ) (_hA : TyDeriv Γ γ A a) (_hx : TmDeriv Γ γ A a x ξ)
    (_hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Ξ T)
    (_hQ : TyDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q)
    (_hp : TmDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q p π) : Inputs :=
  ⟨γ native, a native, ξ native, n, T native, q native, π native⟩

private def inputs := inputsOf NamedCaller.earlier NamedCaller.base NamedCaller.x.deriv
  NamedCaller.generalized NamedCaller.qAtBType NamedCaller.qAtB

theorem tail_length : inputs.length = 3 := rfl

private theorem weaken_value {Γ : RawCtx} {γ : CtxCode.{1}} {A : Expr} {a : TyCode γ}
    (p : BasePoint Γ γ) (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a)
    (z : extendCode γ a native) :
    ((p.weaken hΓ hA).code native).down z = (p.code native).down z.1 := by
  have e := eq_of_heq (castCode_eval (baseSub_code (weakenCode γ a))
    (subTmCode p.code (weakenCode γ a)) native)
  exact congrArg (fun t => t.down z) e

private theorem variable_value {Γ : RawCtx} {γ : CtxCode.{1}}
    (hΓ : CtxDeriv Γ γ) (z : extendCode γ (baseCode γ) native) :
    ((BasePoint.variable hΓ).code native).down z = z.2 := by
  have e := eq_of_heq (castCode_eval (baseSub_code (weakenCode γ (baseCode γ)))
    (varCode γ (baseCode γ)) native)
  exact congrArg (fun t => t.down z) e

/-- The full tail is inhabited, including its dependent identity and fiber
binders, in the native model with varying finite fibers. -/
private def populatedTail : inputs.tail.total := by
  let γ : inputs.context := ⟨PUnit.unit, (3 : Nat)⟩
  let chosen := inputs.point.down γ
  refine ⟨⟨⟨⟨⟨γ, chosen⟩, ⟨⟨rfl⟩⟩⟩, chosen⟩, ⟨⟨?_⟩⟩⟩, ?_⟩
  · simp only [NamedCaller.yAtZ, NamedCaller.moving, NamedCaller.z,
      weaken_value, variable_value]
  · change Fin (_ + 1)
    exact ⟨0, Nat.zero_lt_succ _⟩

theorem tail_inhabited : Nonempty inputs.tail.total := ⟨populatedTail⟩

namespace Candidate
open Contextual

private abbrev g : Contextual.Expression (Fin 6) := .var 0
private abbrev a : Contextual.Expression (Fin 6) := .var 1
private abbrev x : Contextual.Expression (Fin 6) := .var 2
private abbrev t : Contextual.Expression (Fin 6) := .var 3
private abbrev q : Contextual.Expression (Fin 6) := .var 4
private abbrev p : Contextual.Expression (Fin 6) := .var 5
private def premises : Fin 3 → Contextual.Judgment (Fin 6) :=
  ![term g a x, telescope inputs.length (path a x) t, term (total t) q p]
private abbrev assumptions := List.ofFn premises
private def point : Tm (Ω := assumptions) g a x :=
  .hypothesis (List.mem_ofFn.mpr ⟨0, rfl⟩)
private def tail : Tel (Ω := assumptions) inputs.length (path a x) t :=
  .hypothesis (List.mem_ofFn.mpr ⟨1, rfl⟩)
private def value : Tm (Ω := assumptions) (total t) q p :=
  .hypothesis (List.mem_ofFn.mpr ⟨2, rfl⟩)

private def environment : Fin 6 → Value native.toStructuralModel :=
  ![.context inputs.context, .family inputs.context inputs.family,
    .term inputs.context inputs.family inputs.point,
    .telescope _ inputs.length inputs.tail,
    .family inputs.tail.total inputs.valueFamily,
    .term inputs.tail.total inputs.valueFamily inputs.value]

/-- All hypotheses have actual native values, including the three dependent
tail binders. None is a requested equality or a selected-output assumption. -/
theorem assumptions_valid : ∀ j ∈ assumptions, j.eval (Contextual.algebra native) environment := by
  intro j hj
  rcases List.mem_ofFn.mp hj with ⟨i, rfl⟩
  fin_cases i
  · exact ⟨inputs.context, inputs.family, inputs.point, rfl, rfl, rfl⟩
  · refine ⟨_, inputs.tail, ?_, rfl⟩
    simp [Term.eval, Contextual.algebra, Contextual.operation, environment]
  · refine ⟨_, inputs.valueFamily, inputs.value, ?_, rfl, rfl⟩
    simp [Term.eval, Contextual.algebra, Contextual.operation, environment]

private abbrev certificateCommand := DependentAuthorReference.Candidate.certificateCommand point tail value
private abbrev first := DependentAuthorReference.Candidate.firstWeakening value
private abbrev second := DependentAuthorReference.Candidate.secondWeakening value
private abbrev certificateExpression := certificateCommand.expression
private abbrev firstArrow := weaken (total t) (identity q p p)
private abbrev firstContext := extend (total t) (identity q p p)
private abbrev witness := generic (total t) (identity q p p)
private abbrev secondFamily := identity (subTy (identity q p p) firstArrow) witness witness
private abbrev secondArrow := weaken firstContext secondFamily
private abbrev finalContext := extend firstContext secondFamily
private abbrev certificateJudgment := term finalContext
  (subTy (subTy (identity q p p) firstArrow) secondArrow)
  (subTm (subTm certificateExpression firstArrow) secondArrow)

/-- The actual reference certificate judgment is valid after both dependent
weakenings, under satisfied concrete assumptions. -/
theorem certificate_valid : certificateJudgment.eval (Contextual.algebra native) environment :=
  DependentAuthorReference.Candidate.certificateValidity point tail value first second
    native environment assumptions_valid

/-- Constructor admission preserves this full typing judgment in the native
stable Sigma model, beyond equality of an erased old expression. -/
theorem extended_certificate_valid :
    (certificateJudgment.inl Sigma.extraSignature).eval
      (Sigma.algebra native stable.toCapability) environment :=
  DependentAuthorReference.Candidate.extendedValidity point tail value first second
    native stable environment assumptions_valid

/-- This comparison consumes the reference derivation, with the same concrete
three-binder inputs and the certificate-dependent weakening arrows. -/
theorem comparison_valid :
    (Atom.eq (subTm (subTm certificateExpression firstArrow) secondArrow)
      (subTm certificateExpression (Contextual.comp firstArrow secondArrow))).eval
        (Contextual.algebra native) environment :=
  Contextual.interpret (DependentAuthorReference.Candidate.dependentWeakeningComparison
    point tail value) native environment assumptions_valid

private abbrev nativeMotive := native.identity inputs.valueFamily inputs.value inputs.value
private abbrev nativeRoot := native.toStructuralModel.rootTail inputs.family inputs.point inputs.tail
private def nativeCertificate := native.j inputs.family inputs.point inputs.tail nativeMotive
  (native.reflexivity (native.subTy inputs.valueFamily nativeRoot)
    (native.subTm inputs.value nativeRoot))

/-- The evaluated source is the selected J section itself, not merely an
inhabitant of its identity family. -/
theorem selected_certificate : certificateExpression.eval (Contextual.algebra native) environment =
    .term inputs.tail.total nativeMotive nativeCertificate := by
  have decoded :
      (Value.term
        (StructuralModel.Telescope.pullback native.toStructuralModel inputs.tail
          (native.toStructuralModel.rootSub inputs.family inputs.point)).total
        (native.identity (native.subTy inputs.valueFamily nativeRoot)
          (native.subTm inputs.value nativeRoot) (native.subTm inputs.value nativeRoot))
        (native.reflexivity (native.subTy inputs.valueFamily nativeRoot)
          (native.subTm inputs.value nativeRoot))).termAt
        (StructuralModel.Telescope.pullback native.toStructuralModel inputs.tail
          (native.toStructuralModel.rootSub inputs.family inputs.point)).total
        (native.subTy nativeMotive nativeRoot) =
      some (native.reflexivity (native.subTy inputs.valueFamily nativeRoot)
        (native.subTm inputs.value nativeRoot)) :=
    Value.termAt_term _ _ _
  simp [certificateExpression, certificateCommand,
    DependentAuthorReference.Candidate.certificateCommand, Command.expression,
    Term.eval, Contextual.algebra, Contextual.operation,
    DependentJudgments.operation, environment, nativeCertificate,
    Contextual.problem, Contextual.tail, Contextual.point, decoded]

private abbrev nativeFirst := native.weaken inputs.tail.total nativeMotive
private abbrev nativeFirstContext := native.extend inputs.tail.total nativeMotive
private abbrev nativeWitness := native.genericVariable inputs.tail.total nativeMotive
private abbrev nativeSecondFamily := native.identity (native.subTy nativeMotive nativeFirst)
  nativeWitness nativeWitness
private abbrev nativeSecond := native.weaken nativeFirstContext nativeSecondFamily
private abbrev nativeFinalContext := native.extend nativeFirstContext nativeSecondFamily

/-- Extension and both dependent substitutions preserve the exact chosen J
section, including its full family and context. -/
theorem extended_selected_certificate :
    ((subTm (subTm certificateExpression firstArrow) secondArrow).inl
      Sigma.extraSignature).eval (Sigma.algebra native stable.toCapability) environment =
    .term nativeFinalContext (native.subTy (native.subTy nativeMotive nativeFirst) nativeSecond)
      (native.subTm (native.subTm nativeCertificate nativeFirst) nativeSecond) := by
  rw [DependentAuthorReference.Candidate.extensionSelected point tail value
    (σ := firstArrow) (τ := secondArrow) native stable environment]
  have selected := selected_certificate
  simp only [Term.eval, Contextual.algebra, environment] at selected
  simp [Term.eval, Contextual.algebra, Contextual.operation,
    DependentJudgments.operation, environment, selected,
    nativeFirst, nativeSecond, nativeFinalContext, nativeFirstContext,
    nativeSecondFamily, nativeWitness, nativeMotive]

/-- The accepted source command has the same independently frozen recipe. -/
theorem author_recipe : DependentAuthorTrial.Candidate.selected point tail value =
    certificateExpression := rfl

/-- Actual author validity under the inhabited three-binder environment. -/
theorem author_certificate_valid : certificateJudgment.eval (Contextual.algebra native) environment :=
  DependentAuthorTrial.Candidate.certificateValidity point tail value
    (DependentAuthorTrial.Candidate.firstWeakening value)
    (DependentAuthorTrial.Candidate.secondWeakening value) native environment assumptions_valid

/-- This invokes the author's retained derivation and assumption transport. -/
theorem author_extended_certificate_valid :
    (certificateJudgment.inl Sigma.extraSignature).eval
      (Sigma.algebra native stable.toCapability) environment :=
  DependentAuthorTrial.Candidate.extendedTwiceValidity point tail value
    (DependentAuthorTrial.Candidate.firstWeakening value)
    (DependentAuthorTrial.Candidate.secondWeakening value)
    native stable environment assumptions_valid

/-- Source comparison is used at the constructed dependent substitutions. -/
theorem author_comparison_valid :
    (Atom.eq (subTm (subTm certificateExpression firstArrow) secondArrow)
      (subTm certificateExpression (Contextual.comp firstArrow secondArrow))).eval
        (Contextual.algebra native) environment :=
  Contextual.interpret (DependentAuthorTrial.Candidate.dependentWeakeningComparison
    point tail value) native environment assumptions_valid

/-- The author's source recipe selects the same section and dependent family;
no equality-reflection or uniqueness assumption enters this comparison. -/
theorem author_selected_certificate :
    (DependentAuthorTrial.Candidate.selected point tail value).eval
      (Contextual.algebra native) environment =
      .term inputs.tail.total nativeMotive nativeCertificate :=
  selected_certificate

/-- The author's extension theorem, combined with evaluation of the selected
section, retains the exact twice-substituted J value in the concrete model. -/
theorem author_extended_selected_certificate :
    ((subTm (subTm (DependentAuthorTrial.Candidate.selected point tail value) firstArrow)
      secondArrow).inl Sigma.extraSignature).eval
        (Sigma.algebra native stable.toCapability) environment =
    .term nativeFinalContext (native.subTy (native.subTy nativeMotive nativeFirst) nativeSecond)
      (native.subTm (native.subTm nativeCertificate nativeFirst) nativeSecond) := by
  rw [(DependentAuthorTrial.Candidate.extensionSelectedTwice point tail value
    (DependentAuthorTrial.Candidate.firstWeakening value)
    (DependentAuthorTrial.Candidate.secondWeakening value)
    native stable environment assumptions_valid).2]
  have selected := author_selected_certificate
  simp only [Term.eval, Contextual.algebra, environment] at selected
  simp [Term.eval, Contextual.algebra, Contextual.operation,
    DependentJudgments.operation, environment, selected,
    nativeFirst, nativeSecond, nativeFinalContext, nativeFirstContext,
    nativeSecondFamily, nativeWitness, nativeMotive]

end Candidate

namespace Constructor
private abbrev A : native.Family Nat := fun n => Fin (n + 1)
private abbrev B : native.Family (native.extend Nat A) := fun p => Fin (p.2.val + 1)
private def shift : native.Substitution Nat Nat := ⟨fun n => n + 1⟩
private def double : native.Substitution Nat Nat := ⟨fun n => 2 * n⟩

/-- Repeated reindexing compares actual varying Sigma families, including the
second family's dependence on the selected first component. -/
theorem sigma_composition :
    stable.sigma (native.subTy (native.subTy A shift) double)
      (native.subTy (native.subTy B (native.toStructuralModel.lift A shift))
        (native.toStructuralModel.lift (native.subTy A shift) double)) =
    stable.sigma (native.subTy A (native.compSub shift double))
      (native.subTy B (native.toStructuralModel.lift A (native.compSub shift double))) :=
  stable.sigma_comp A B shift double

theorem substitution_order :
    (native.compSub shift double).down 1 = 3 ∧
      (native.compSub double shift).down 1 = 4 := ⟨rfl, rfl⟩

/-- The selected bounded index is retained by dependent pair elimination. -/
theorem selected_index :
    ((Sigma.Native.capability Unit (fun _ => Unit)).split (fun _ : Unit => Nat)
      (fun p => Fin (p.2 + 1)) (fun p => Fin (p.2.1 + 1))
      ⟨Sigma.Native.boundedBranch⟩).down ⟨(), 3, (⟨2, by decide⟩ : Fin 4)⟩ =
        (⟨2, by decide⟩ : Fin 4) :=
  Sigma.Native.bounded_split 3 (⟨2, by decide⟩ : Fin 4)

/-- The same nonconstant motive satisfies the generic beta law as a section,
not just the displayed point calculation. -/
theorem bounded_beta :
    HEq ((NativeType.structuralModel Unit (fun _ => Unit)).subTm
      ((Sigma.Native.capability Unit (fun _ => Unit)).split (fun _ : Unit => Nat)
        (fun p => Fin (p.2 + 1)) (fun p => Fin (p.2.1 + 1)) ⟨Sigma.Native.boundedBranch⟩)
      ((Sigma.Native.capability Unit (fun _ => Unit)).pack (fun _ : Unit => Nat)
        (fun p => Fin (p.2 + 1)))) (ULift.up Sigma.Native.boundedBranch) :=
  Sigma.Native.bounded_beta

end Constructor
end Examples.DependentAuthorTrialCases
