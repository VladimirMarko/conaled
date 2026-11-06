import Examples.FrozenMemoReindex

/-! The varying certificate family and its selected dependent action. -/
noncomputable section
namespace Examples.FrozenMemoRealization
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open SquareKit.Internal.DependentJudgments.Contextual.Memo
open Examples.GuardedGroupoidMemo
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false
universe u
variable {M : SquareKit.Internal.PathTransport.Typed.Model.{u}} {V : Type}
variable {Ω : List (Contextual.Judgment V)} {ρ : V → Value M.toStructuralModel}
namespace InputRealization
variable {F : Frozen.Input Ω} (R : InputRealization M ρ F)
variable (hΩ : ∀ j ∈ Ω, j.eval (Contextual.algebra M) ρ)

def varying : InputRealization M ρ
    (F.reindex F.parameters.pathType_typed.weaken) := by
  let A := M.identity R.family R.x R.y
  have hA := identity_eval M ρ F.A F.x F.y R.context R.family R.x R.y
    R.family_eval R.x_eval R.y_eval
  exact R.reindex F.parameters.pathType_typed.weaken (M.extend R.context A)
    (M.weaken R.context A)
    (extend_eval M ρ F.Γ F.parameters.pathType R.context A R.context_eval hA)
    (weaken_eval M ρ F.Γ F.parameters.pathType R.context A R.context_eval hA)

def varyingPath : M.Section R.varying.context
    (M.identity R.varying.family R.varying.x R.varying.y) :=
  cast (congrArg (M.Section R.varying.context)
    (M.identity_sub R.family R.x R.y (M.weaken R.context (M.identity R.family R.x R.y))))
    (M.genericVariable R.context (M.identity R.family R.x R.y))


def varyingValue := transportValue M (Γ := R.varying.context) R.varying.family
  R.varying.fiber
  R.varying.y R.varying.z R.varying.q
  (transportValue M R.varying.family R.varying.fiber
    R.varying.x R.varying.y R.varyingPath R.varying.element)

def varyingComposite := transportValue M (Γ := R.varying.context) R.varying.family
  R.varying.fiber
  R.varying.x R.varying.z
  (concatValue M R.varying.family R.varying.x R.varying.y R.varying.z
    R.varyingPath R.varying.q) R.varying.element

def certificateFamily : (M).Family R.varying.context :=
  (M).identity (M.subTy R.varying.fiber (M.toStructuralModel.sectionSub R.varying.family R.varying.z)) R.varyingValue R.varyingComposite

def certificateSection := etaValue M (Γ := R.varying.context) R.varying.family
  R.varying.fiber
  R.varying.x R.varying.y R.varying.z R.varyingPath R.varying.q R.varying.element

theorem certificateSection_eval : F.parameters.certificateSection.eval (Contextual.algebra M) ρ =
    .term R.varying.context R.certificateFamily R.certificateSection := by
  have hA := identity_eval M ρ F.A F.x F.y R.context R.family R.x R.y
    R.family_eval R.x_eval R.y_eval
  have hp := generic_eval M ρ F.Γ F.parameters.pathType R.context
    (M.identity R.family R.x R.y) R.context_eval hA
  exact eta_eval M ρ F.parameters.varying.Γ F.parameters.varying.A F.parameters.varying.B
    F.parameters.varying.x F.parameters.varying.y F.parameters.varying.z
    F.parameters.variablePath F.parameters.varying.q F.parameters.varying.u
    R.varying.context R.varying.family R.varying.fiber
    R.varying.x R.varying.y R.varying.z R.varyingPath R.varying.q R.varying.element
    R.varying.context_eval R.varying.family_eval R.varying.fiber_eval
    R.varying.x_eval R.varying.y_eval R.varying.z_eval
    (converted_eval M ρ (M.identity_sub R.family R.x R.y
      (M.weaken R.context (M.identity R.family R.x R.y))) _ hp) R.varying.q_eval R.varying.element_eval

include hΩ in
theorem certificateFamily_eval : F.parameters.certificateFamily.eval (Contextual.algebra M) ρ =
    .family R.varying.context R.certificateFamily :=
  family_of_eval M ρ F.parameters.certificateSection_typed hΩ _ _ _ R.certificateSection_eval

def atPath := (M).toStructuralModel.sectionSub (M.identity R.family R.x R.y) R.p
def atParallelPath := (M).toStructuralModel.sectionSub (M.identity R.family R.x R.y) R.p'
def certificateAtPath := (M).subTm R.certificateSection R.atPath
def certificateAtParallelPath := (M).subTm R.certificateSection R.atParallelPath

def transportedCertificate := transportValue M (Γ := R.context)
  (M.identity R.family R.x R.y) R.certificateFamily
  R.p R.p' R.h R.certificateAtPath

def dependentActionFamily := (M).identity ((M).subTy R.certificateFamily R.atParallelPath)
  R.transportedCertificate R.certificateAtParallelPath

theorem certificateAtPath_eval : (F.parameters.certificate F.p).eval (Contextual.algebra M) ρ =
    .term R.context ((M).subTy R.certificateFamily R.atPath) R.certificateAtPath := by
  have hA := identity_eval M ρ F.A F.x F.y R.context R.family R.x R.y
    R.family_eval R.x_eval R.y_eval
  have hs := sectionSub_eval M ρ F.Γ F.parameters.pathType F.p R.context
    (M.identity R.family R.x R.y) R.p R.context_eval hA R.p_eval
  exact subTm_eval M ρ F.parameters.certificateSection (F.parameters.atPath F.p) _ _
    R.certificateFamily R.certificateSection R.atPath R.certificateSection_eval hs

include hΩ in
theorem transportedCertificate_eval : (F.parameters.transportedCertificate F.p F.p' F.h).eval
    (Contextual.algebra M) ρ =
    .term R.context ((M).subTy R.certificateFamily R.atParallelPath) R.transportedCertificate := by
  have hA := identity_eval M ρ F.A F.x F.y R.context R.family R.x R.y
    R.family_eval R.x_eval R.y_eval
  exact transport_eval M ρ F.Γ F.parameters.pathType F.parameters.certificateFamily F.p F.p' F.h
    (F.parameters.certificate F.p) R.context (M.identity R.family R.x R.y) R.certificateFamily
    R.p R.p' R.h R.certificateAtPath R.context_eval hA
    (R.certificateFamily_eval hΩ) R.p_eval R.p'_eval R.h_eval R.certificateAtPath_eval

/-- The dependent action's domain is transport in the certificate family.
It is not replaced with the untransported certificate at the first path. -/
def dependentAction := apdValue M (Γ := R.context)
  (M.identity R.family R.x R.y) R.certificateFamily
  R.p R.p' R.h R.certificateSection

include hΩ in
theorem dependentAction_eval : (F.parameters.dependentAction F.p F.p' F.h).eval (Contextual.algebra M) ρ =
    .term R.context R.dependentActionFamily R.dependentAction := by
  have hA := identity_eval M ρ F.A F.x F.y R.context R.family R.x R.y
    R.family_eval R.x_eval R.y_eval
  exact apd_eval M ρ F.Γ F.parameters.pathType F.parameters.certificateFamily
    F.p F.p' F.h F.parameters.certificateSection R.context
    (M.identity R.family R.x R.y) R.certificateFamily R.p R.p' R.h
    R.certificateSection R.context_eval hA (R.certificateFamily_eval hΩ)
    R.p_eval R.p'_eval R.h_eval R.certificateSection_eval

include hΩ in
/-- The parsed source type agrees with the semantic type, with the transported
certificate as its first endpoint. -/
theorem dependentActionFamily_eval :
    (Contextual.identity (F.parameters.certificateType F.p')
      (F.parameters.transportedCertificate F.p F.p' F.h) (F.parameters.certificate F.p')).eval
      (Contextual.algebra M) ρ = .family R.context R.dependentActionFamily :=
  family_of_eval M ρ (F.parameters.dependentAction_typed F.hp F.hp' F.hh) hΩ
    R.context R.dependentActionFamily R.dependentAction (R.dependentAction_eval hΩ)

end InputRealization
end Examples.FrozenMemoRealization
