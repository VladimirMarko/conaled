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

def memoValueSubComp := I.parameters.valueSubComp I.hp hσ hτ
def memoFiberSubComp := I.parameters.fiberSubComp I.hp hσ hτ
def memoCertificateSubComp := I.parameters.certificateSubComp I.hp hσ hτ
def memoCertificateTypeSubComp := I.parameters.certificateTypeSubComp I.hp hσ hτ
def memoActionSubComp := I.parameters.dependentActionSubComp I.hp I.hp' I.hh hσ hτ
def memoTransportedSourceSubComp := I.parameters.transportedCertificateSubComp I.hp I.hp' I.hh hσ hτ
def memoActionTypeSubComp := I.parameters.dependentActionTypeSubComp I.hp I.hp' I.hh hσ hτ

def memoValueReindex : Equal (Ω := Ω) (subTm (I.parameters.value I.p) σ)
    ((I.reindex hσ).parameters.value (subTm I.p σ)) :=
  I.parameters.valueReindex I.hp hσ

def memoCertificateReindex : Equal (Ω := Ω) (subTm (I.parameters.certificate I.p) σ)
    ((I.reindex hσ).parameters.certificate (subTm I.p σ)) :=
  I.parameters.certificateReindex I.hp hσ

def memoFiberReindex : Equal (Ω := Ω) (subTy (I.parameters.fiber I.p) σ)
    ((I.reindex hσ).parameters.fiber (subTm I.p σ)) :=
  I.parameters.fiberReindex I.hp hσ

def memoCertificateTypeReindex : Equal (Ω := Ω) (subTy (I.parameters.certificateType I.p) σ)
    ((I.reindex hσ).parameters.certificateType (subTm I.p σ)) :=
  I.parameters.certificateTypeReindex I.hp hσ

def memoValueTwice : Equal (Ω := Ω) (subTm (subTm (I.parameters.value I.p) σ) τ)
    (((I.reindex hσ).reindex hτ).parameters.value (subTm (subTm I.p σ) τ)) :=
  (Equal.subTm (I.memoValueReindex hσ) (.reflexive τ)).transitive
    ((I.reindex hσ).memoValueReindex hτ)

def memoCertificateTwice : Equal (Ω := Ω) (subTm (subTm (I.parameters.certificate I.p) σ) τ)
    (((I.reindex hσ).reindex hτ).parameters.certificate (subTm (subTm I.p σ) τ)) :=
  (Equal.subTm (I.memoCertificateReindex hσ) (.reflexive τ)).transitive
    ((I.reindex hσ).memoCertificateReindex hτ)

def memoActionReindex : Equal (Ω := Ω) (subTm (I.parameters.dependentAction I.p I.p' I.h) σ)
    ((I.reindex hσ).parameters.dependentAction (subTm I.p σ) (subTm I.p' σ) (subTm I.h σ)) :=
  I.parameters.dependentActionFresh hσ I.hp I.hp' I.hh

def memoTransportedSourceReindex : Equal (Ω := Ω) (subTm (I.parameters.transportedCertificate I.p I.p' I.h) σ)
    ((I.reindex hσ).parameters.transportedCertificate (subTm I.p σ) (subTm I.p' σ) (subTm I.h σ)) :=
  I.parameters.transportedCertificateFresh hσ I.hp I.hp' I.hh

def memoActionTwice : Equal (Ω := Ω) (subTm (subTm (I.parameters.dependentAction I.p I.p' I.h) σ) τ)
    (((I.reindex hσ).reindex hτ).parameters.dependentAction
      (subTm (subTm I.p σ) τ) (subTm (subTm I.p' σ) τ) (subTm (subTm I.h σ) τ)) :=
  (Equal.subTm (I.memoActionReindex hσ) (.reflexive τ)).transitive
    ((I.reindex hσ).memoActionReindex hτ)

def memoTransportedSourceTwice : Equal (Ω := Ω) (subTm (subTm (I.parameters.transportedCertificate I.p I.p' I.h) σ) τ)
    (((I.reindex hσ).reindex hτ).parameters.transportedCertificate
      (subTm (subTm I.p σ) τ) (subTm (subTm I.p' σ) τ) (subTm (subTm I.h σ) τ)) :=
  (Equal.subTm (I.memoTransportedSourceReindex hσ) (.reflexive τ)).transitive
    ((I.reindex hσ).memoTransportedSourceReindex hτ)

end Input

namespace Signature
variable (S : Signature Ω)

/-- Successive frozen assignments versus their composite, for the value. -/
def valueSubComp := S.input.memoValueSubComp S.sigmaTyping S.tauTyping
def fiberSubComp := S.input.memoFiberSubComp S.sigmaTyping S.tauTyping
def certificateSubComp := S.input.memoCertificateSubComp S.sigmaTyping S.tauTyping
def certificateTypeSubComp := S.input.memoCertificateTypeSubComp S.sigmaTyping S.tauTyping
def dependentActionSubComp := S.input.memoActionSubComp S.sigmaTyping S.tauTyping
def transportedCertificateSubComp := S.input.memoTransportedSourceSubComp S.sigmaTyping S.tauTyping
def dependentActionTypeSubComp := S.input.memoActionTypeSubComp S.sigmaTyping S.tauTyping

/-- The first assignment reconstructs the actual selected memo. -/
def valueSigma := S.input.memoValueReindex S.sigmaTyping
def certificateSigma := S.input.memoCertificateReindex S.sigmaTyping
def fiberSigma := S.input.memoFiberReindex S.sigmaTyping
def certificateTypeSigma := S.input.memoCertificateTypeReindex S.sigmaTyping

/-- The second assignment reconstructs the selected memo over Theta. -/
def valueTau := S.deltaInput.memoValueReindex S.tauTyping
def certificateTau := S.deltaInput.memoCertificateReindex S.tauTyping
def fiberTau := S.deltaInput.memoFiberReindex S.tauTyping
def certificateTypeTau := S.deltaInput.memoCertificateTypeReindex S.tauTyping

def valueTwice := S.input.memoValueTwice S.sigmaTyping S.tauTyping
def certificateTwice := S.input.memoCertificateTwice S.sigmaTyping S.tauTyping

def dependentActionSigma := S.input.memoActionReindex S.sigmaTyping
def transportedCertificateSigma := S.input.memoTransportedSourceReindex S.sigmaTyping
def dependentActionTau := S.deltaInput.memoActionReindex S.tauTyping
def transportedCertificateTau := S.deltaInput.memoTransportedSourceReindex S.tauTyping
def dependentActionTwice := S.input.memoActionTwice S.sigmaTyping S.tauTyping
def transportedCertificateTwice := S.input.memoTransportedSourceTwice S.sigmaTyping S.tauTyping

def valueFormula := S.input.parameters.valueAtPath S.input.hp
def certificateFormula := S.input.parameters.certificateAtPath S.input.hp
def deltaValueFormula := S.deltaInput.parameters.valueAtPath S.deltaInput.hp
def deltaCertificateFormula := S.deltaInput.parameters.certificateAtPath S.deltaInput.hp
def thetaValueFormula := S.thetaInput.parameters.valueAtPath S.thetaInput.hp
def thetaCertificateFormula := S.thetaInput.parameters.certificateAtPath S.thetaInput.hp

def normalizedDependentActionTyping := S.input.parameters.normalizedDependentActionTyping S.input.hp S.input.hp' S.input.hh
def deltaNormalizedDependentActionTyping := S.deltaInput.parameters.normalizedDependentActionTyping S.deltaInput.hp S.deltaInput.hp' S.deltaInput.hh
def thetaNormalizedDependentActionTyping := S.thetaInput.parameters.normalizedDependentActionTyping S.thetaInput.hp S.thetaInput.hp' S.thetaInput.hh

end Signature
end
end SquareKit.Internal.DependentJudgments.Contextual.Memo.Frozen
