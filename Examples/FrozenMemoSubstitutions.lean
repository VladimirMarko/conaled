import Examples.FrozenMemoDependentAction

/-! The original frozen maps preserve the selected certificate and its dependent
 action, with the family reindexed along exactly the same two maps. -/
noncomputable section
namespace Examples.FrozenMemoRealization
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.DependentJudgments.Contextual.Memo
open Examples.GuardedGroupoidMemo
universe u
variable (M : SquareKit.Internal.PathTransport.Typed.Model.{u}) {V : Type}
variable {Ω : List (Contextual.Judgment V)} (ρ : V → Value M.toStructuralModel)
variable (hΩ : ∀ j ∈ Ω, j.eval (Contextual.algebra M) ρ)
variable (S : Frozen.Signature Ω)
variable (deltaRealization : InputRealization M ρ S.deltaInput)
variable (thetaRealization : InputRealization M ρ S.thetaInput)

/- The selected certificate is preserved at each constructed assignment. -/
include hΩ in
theorem certificate_sigma_eval :
    (Contextual.subTm (S.input.parameters.certificate S.input.p) S.sigma).eval
      (Contextual.algebra M) ρ =
      .term deltaRealization.context _ deltaRealization.selectedCertificate :=
  (Contextual.interpret S.certificateSigma M ρ hΩ).trans
    (deltaRealization.certificate_eval hΩ)

include hΩ in
theorem certificate_tau_eval :
    (Contextual.subTm (S.deltaInput.parameters.certificate S.deltaInput.p) S.tau).eval
      (Contextual.algebra M) ρ =
      .term thetaRealization.context _ thetaRealization.selectedCertificate :=
  (Contextual.interpret S.certificateTau M ρ hΩ).trans
    (thetaRealization.certificate_eval hΩ)

include hΩ in
theorem certificate_twice_eval :
    (Contextual.subTm (Contextual.subTm (S.input.parameters.certificate S.input.p) S.sigma)
      S.tau).eval (Contextual.algebra M) ρ =
      .term thetaRealization.context _ thetaRealization.selectedCertificate :=
  (Contextual.interpret S.certificateTwice M ρ hΩ).trans
    (thetaRealization.certificate_eval hΩ)

/- Each result is the action of the freshly constructed varying certificate
section, in its full transported-source type. -/
include hΩ in
theorem dependentAction_sigma_eval :
    (Contextual.subTm (S.input.parameters.dependentAction S.input.p S.input.p' S.input.h)
      S.sigma).eval (Contextual.algebra M) ρ =
      .term deltaRealization.context deltaRealization.dependentActionFamily deltaRealization.dependentAction :=
  (Contextual.interpret S.dependentActionSigma M ρ hΩ).trans
    (deltaRealization.dependentAction_eval hΩ)

include hΩ in
theorem dependentAction_tau_eval :
    (Contextual.subTm (S.deltaInput.parameters.dependentAction S.deltaInput.p S.deltaInput.p' S.deltaInput.h)
      S.tau).eval (Contextual.algebra M) ρ =
      .term thetaRealization.context thetaRealization.dependentActionFamily thetaRealization.dependentAction :=
  (Contextual.interpret S.dependentActionTau M ρ hΩ).trans
    (thetaRealization.dependentAction_eval hΩ)

include hΩ in
theorem dependentAction_twice_eval :
    (Contextual.subTm (Contextual.subTm
      (S.input.parameters.dependentAction S.input.p S.input.p' S.input.h) S.sigma)
      S.tau).eval (Contextual.algebra M) ρ =
      .term thetaRealization.context thetaRealization.dependentActionFamily thetaRealization.dependentAction :=
  (Contextual.interpret S.dependentActionTwice M ρ hΩ).trans
    (thetaRealization.dependentAction_eval hΩ)

include hΩ in
theorem transportedCertificate_sigma_eval :
    (Contextual.subTm (S.input.parameters.transportedCertificate S.input.p S.input.p' S.input.h)
      S.sigma).eval (Contextual.algebra M) ρ =
      .term deltaRealization.context _ deltaRealization.transportedCertificate :=
  (Contextual.interpret S.transportedCertificateSigma M ρ hΩ).trans
    (deltaRealization.transportedCertificate_eval hΩ)

include hΩ in
theorem transportedCertificate_tau_eval :
    (Contextual.subTm (S.deltaInput.parameters.transportedCertificate S.deltaInput.p S.deltaInput.p' S.deltaInput.h)
      S.tau).eval (Contextual.algebra M) ρ =
      .term thetaRealization.context _ thetaRealization.transportedCertificate :=
  (Contextual.interpret S.transportedCertificateTau M ρ hΩ).trans
    (thetaRealization.transportedCertificate_eval hΩ)

include hΩ in
theorem transportedCertificate_twice_eval :
    (Contextual.subTm (Contextual.subTm
      (S.input.parameters.transportedCertificate S.input.p S.input.p' S.input.h) S.sigma)
      S.tau).eval (Contextual.algebra M) ρ =
      .term thetaRealization.context _ thetaRealization.transportedCertificate :=
  (Contextual.interpret S.transportedCertificateTwice M ρ hΩ).trans
    (thetaRealization.transportedCertificate_eval hΩ)

/- The twice-substituted dependent-action type retains its transported source. -/
include hΩ in
theorem dependentAction_type_twice_eval :
    (Contextual.subTy (Contextual.subTy
      (Contextual.identity (S.input.parameters.certificateType S.input.p')
        (S.input.parameters.transportedCertificate S.input.p S.input.p' S.input.h)
        (S.input.parameters.certificate S.input.p')) S.sigma) S.tau).eval
      (Contextual.algebra M) ρ =
      .family thetaRealization.context thetaRealization.dependentActionFamily :=
  family_of_eval M ρ
    (((S.input.parameters.dependentActionTyping S.input.hp S.input.hp' S.input.hh).substitute
      S.sigmaTyping).substitute S.tauTyping) hΩ
    thetaRealization.context thetaRealization.dependentActionFamily thetaRealization.dependentAction (dependentAction_twice_eval M ρ hΩ S thetaRealization)


end Examples.FrozenMemoRealization
