import SquareKit.Internal.DependentJudgments.FrozenContexts
import SquareKit.Internal.DependentJudgments.MemoFreshAction

/-! The generated memo at the two constructed frozen object substitutions.
The equations retain the chosen certificate and the transported source of its
induced dependent action. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Memo.Frozen
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {V : Type} {Ω : List (Judgment V)}

namespace Input
variable (I : Input Ω) {Δ Θ σ τ : Expression V}
  (hσ : Sub (Ω := Ω) Δ I.Γ σ) (hτ : Sub (Ω := Ω) Θ Δ τ)

def memoValue_subComp := I.parameters.value_subComp I.hp hσ hτ
def memoFiber_subComp := I.parameters.fiber_subComp I.hp hσ hτ
def memoCertificate_subComp := I.parameters.certificate_subComp I.hp hσ hτ
def memoCertificateType_subComp := I.parameters.certificateType_subComp I.hp hσ hτ
def memoAction_subComp := I.parameters.dependentAction_subComp I.hp I.hp' I.hh hσ hτ
def memoTransportedSource_subComp := I.parameters.transportedCertificate_subComp I.hp I.hp' I.hh hσ hτ
def memoActionType_subComp := I.parameters.dependentActionType_subComp I.hp I.hp' I.hh hσ hτ

def memoValue_reindex : Equal (Ω := Ω) (subTm (I.parameters.value I.p) σ)
    ((I.reindex hσ).parameters.value (subTm I.p σ)) :=
  I.parameters.value_reindex I.hp hσ

def memoCertificate_reindex : Equal (Ω := Ω) (subTm (I.parameters.certificate I.p) σ)
    ((I.reindex hσ).parameters.certificate (subTm I.p σ)) :=
  I.parameters.certificate_reindex I.hp hσ

def memoFiber_reindex : Equal (Ω := Ω) (subTy (I.parameters.fiber I.p) σ)
    ((I.reindex hσ).parameters.fiber (subTm I.p σ)) :=
  I.parameters.fiber_reindex I.hp hσ

def memoCertificateType_reindex : Equal (Ω := Ω) (subTy (I.parameters.certificateType I.p) σ)
    ((I.reindex hσ).parameters.certificateType (subTm I.p σ)) :=
  I.parameters.certificateType_reindex I.hp hσ

def memoValue_twice : Equal (Ω := Ω) (subTm (subTm (I.parameters.value I.p) σ) τ)
    (((I.reindex hσ).reindex hτ).parameters.value (subTm (subTm I.p σ) τ)) :=
  (Equal.subTm (I.memoValue_reindex hσ) (.reflexive τ)).transitive
    ((I.reindex hσ).memoValue_reindex hτ)

def memoCertificate_twice : Equal (Ω := Ω) (subTm (subTm (I.parameters.certificate I.p) σ) τ)
    (((I.reindex hσ).reindex hτ).parameters.certificate (subTm (subTm I.p σ) τ)) :=
  (Equal.subTm (I.memoCertificate_reindex hσ) (.reflexive τ)).transitive
    ((I.reindex hσ).memoCertificate_reindex hτ)

def memoAction_reindex : Equal (Ω := Ω) (subTm (I.parameters.dependentAction I.p I.p' I.h) σ)
    ((I.reindex hσ).parameters.dependentAction (subTm I.p σ) (subTm I.p' σ) (subTm I.h σ)) :=
  I.parameters.dependentAction_fresh hσ I.hp I.hp' I.hh

def memoTransportedSource_reindex : Equal (Ω := Ω) (subTm (I.parameters.transportedCertificate I.p I.p' I.h) σ)
    ((I.reindex hσ).parameters.transportedCertificate (subTm I.p σ) (subTm I.p' σ) (subTm I.h σ)) :=
  I.parameters.transportedCertificate_fresh hσ I.hp I.hp' I.hh

def memoAction_twice : Equal (Ω := Ω) (subTm (subTm (I.parameters.dependentAction I.p I.p' I.h) σ) τ)
    (((I.reindex hσ).reindex hτ).parameters.dependentAction
      (subTm (subTm I.p σ) τ) (subTm (subTm I.p' σ) τ) (subTm (subTm I.h σ) τ)) :=
  (Equal.subTm (I.memoAction_reindex hσ) (.reflexive τ)).transitive
    ((I.reindex hσ).memoAction_reindex hτ)

def memoTransportedSource_twice : Equal (Ω := Ω) (subTm (subTm (I.parameters.transportedCertificate I.p I.p' I.h) σ) τ)
    (((I.reindex hσ).reindex hτ).parameters.transportedCertificate
      (subTm (subTm I.p σ) τ) (subTm (subTm I.p' σ) τ) (subTm (subTm I.h σ) τ)) :=
  (Equal.subTm (I.memoTransportedSource_reindex hσ) (.reflexive τ)).transitive
    ((I.reindex hσ).memoTransportedSource_reindex hτ)

end Input

namespace Signature
variable (S : Signature Ω)

/-- Successive frozen assignments versus their composite, for the value. -/
def value_subComp := S.input.memoValue_subComp S.sigma_typed S.tau_typed
def fiber_subComp := S.input.memoFiber_subComp S.sigma_typed S.tau_typed
def certificate_subComp := S.input.memoCertificate_subComp S.sigma_typed S.tau_typed
def certificateType_subComp := S.input.memoCertificateType_subComp S.sigma_typed S.tau_typed
def dependentAction_subComp := S.input.memoAction_subComp S.sigma_typed S.tau_typed
def transportedCertificate_subComp := S.input.memoTransportedSource_subComp S.sigma_typed S.tau_typed
def dependentActionType_subComp := S.input.memoActionType_subComp S.sigma_typed S.tau_typed

/-- The first assignment reconstructs the actual selected memo. -/
def value_sigma := S.input.memoValue_reindex S.sigma_typed
def certificate_sigma := S.input.memoCertificate_reindex S.sigma_typed
def fiber_sigma := S.input.memoFiber_reindex S.sigma_typed
def certificateType_sigma := S.input.memoCertificateType_reindex S.sigma_typed

/-- The second assignment reconstructs the selected memo over Theta. -/
def value_tau := S.deltaInput.memoValue_reindex S.tau_typed
def certificate_tau := S.deltaInput.memoCertificate_reindex S.tau_typed
def fiber_tau := S.deltaInput.memoFiber_reindex S.tau_typed
def certificateType_tau := S.deltaInput.memoCertificateType_reindex S.tau_typed

def value_twice := S.input.memoValue_twice S.sigma_typed S.tau_typed
def certificate_twice := S.input.memoCertificate_twice S.sigma_typed S.tau_typed

def dependentAction_sigma := S.input.memoAction_reindex S.sigma_typed
def transportedCertificate_sigma := S.input.memoTransportedSource_reindex S.sigma_typed
def dependentAction_tau := S.deltaInput.memoAction_reindex S.tau_typed
def transportedCertificate_tau := S.deltaInput.memoTransportedSource_reindex S.tau_typed
def dependentAction_twice := S.input.memoAction_twice S.sigma_typed S.tau_typed
def transportedCertificate_twice := S.input.memoTransportedSource_twice S.sigma_typed S.tau_typed

def value_formula := S.input.parameters.value_atPath S.input.hp
def certificate_formula := S.input.parameters.certificate_atPath S.input.hp
def deltaValue_formula := S.deltaInput.parameters.value_atPath S.deltaInput.hp
def deltaCertificate_formula := S.deltaInput.parameters.certificate_atPath S.deltaInput.hp
def thetaValue_formula := S.thetaInput.parameters.value_atPath S.thetaInput.hp
def thetaCertificate_formula := S.thetaInput.parameters.certificate_atPath S.thetaInput.hp

def dependentAction_normalized := S.input.parameters.dependentAction_normalized S.input.hp S.input.hp' S.input.hh
def deltaDependentAction_normalized := S.deltaInput.parameters.dependentAction_normalized S.deltaInput.hp S.deltaInput.hp' S.deltaInput.hh
def thetaDependentAction_normalized := S.thetaInput.parameters.dependentAction_normalized S.thetaInput.hp S.thetaInput.hp' S.thetaInput.hh

end Signature
end
end SquareKit.Internal.DependentJudgments.Contextual.Memo.Frozen
