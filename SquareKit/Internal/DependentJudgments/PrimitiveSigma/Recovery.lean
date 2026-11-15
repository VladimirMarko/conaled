import SquareKit.Internal.DependentJudgments.PrimitiveSigma.Reindexing
import SquareKit.Internal.DependentJudgments.Memo

/-! Named old arguments and selected data survive constructor admission. These
are exact reduct statements, conditional on the supplied Sigma capability;
they do not assert expansion of every old model. -/
namespace SquareKit.Internal.DependentJudgments.PrimitiveSigma
open GuardedTheory PathTransport.Typed
universe u
variable {V : Type} {Ω : List (Contextual.Judgment V)}
variable (F : Contextual.Memo.Parameters Ω)

/-- The selected certificate section is retained as the same source argument. -/
noncomputable def retain_certificate : Derivation theory (Ω.map (Atom.inl extraSignature))
    ((Contextual.term F.pathContext F.certificateFamily F.certificateSection).inl extraSignature) :=
  retain F.certificateSection_typed

/-- The higher dependent action keeps its transported source boundary. -/
noncomputable def retain_dependentAction {p p' h : Contextual.Expression V}
    (hp : Contextual.Tm (Ω := Ω) F.Γ F.pathType p)
    (hp' : Contextual.Tm (Ω := Ω) F.Γ F.pathType p')
    (hh : Contextual.Tm (Ω := Ω) F.Γ (Contextual.identity F.pathType p p') h) :
    Derivation theory (Ω.map (Atom.inl extraSignature))
      ((Contextual.term F.Γ
        (Contextual.identity (F.certificateType p') (F.transportedCertificate p p' h) (F.certificate p'))
        (F.dependentAction p p' h)).inl extraSignature) :=
  retain (F.dependentAction_typed hp hp' hh)

variable (M : PathTransport.Typed.Model.{u}) (S : Capability M.toStructuralModel)
  (ρ : V → Value M.toStructuralModel)

/-- Exact selected data, not merely inhabitation or endpoint equality. -/
theorem recover_certificate :
    (F.certificateSection.inl extraSignature).eval (algebra M S) ρ =
      F.certificateSection.eval (Contextual.algebra M) ρ := eval_old M S _ ρ

theorem recover_dependentAction (p p' h : Contextual.Expression V) :
    ((F.dependentAction p p' h).inl extraSignature).eval (algebra M S) ρ =
      (F.dependentAction p p' h).eval (Contextual.algebra M) ρ := eval_old M S _ ρ

theorem recover_transportedSource (p p' h : Contextual.Expression V) :
    ((F.transportedCertificate p p' h).inl extraSignature).eval (algebra M S) ρ =
      (F.transportedCertificate p p' h).eval (Contextual.algebra M) ρ := eval_old M S _ ρ

theorem recover_value (p : Contextual.Expression V) :
    ((F.value p).inl extraSignature).eval (algebra M S) ρ =
      (F.value p).eval (Contextual.algebra M) ρ := eval_old M S _ ρ

/-- The selected certificate survives both constructor admission and the later
substitution-law extension. -/
noncomputable def retain_certificate_twice : Derivation Reindexing.theory
    (Ω.map (Atom.inl extraSignature))
    ((Contextual.term F.pathContext F.certificateFamily F.certificateSection).inl extraSignature) :=
  Reindexing.retain (retain_certificate F)

theorem recover_certificate_twice (T : Stable M.toStructuralModel) :
    (F.certificateSection.inl extraSignature).eval (Reindexing.model M T).toAlgebra ρ =
      F.certificateSection.eval (Contextual.algebra M) ρ := eval_old M T.toCapability _ ρ

theorem recover_dependentAction_twice (T : Stable M.toStructuralModel)
    (p p' h : Contextual.Expression V) :
    ((F.dependentAction p p' h).inl extraSignature).eval (Reindexing.model M T).toAlgebra ρ =
      (F.dependentAction p p' h).eval (Contextual.algebra M) ρ := eval_old M T.toCapability _ ρ

end SquareKit.Internal.DependentJudgments.PrimitiveSigma
