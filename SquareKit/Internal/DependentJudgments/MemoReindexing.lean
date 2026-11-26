import SquareKit.Internal.DependentJudgments.MemoNormalization

/-! Reindexing the actual memo package agrees with reconstructing its selected
value and certificate from reindexed parameters. Dependent action retains the
reindexed certificate section and its transported source. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Memo.Parameters
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {V : Type} {Ω : List (Judgment V)} (F : Parameters Ω)
variable {Δ σ p : Expression V} (hp : Tm (Ω := Ω) F.Γ F.pathType p) (hσ : Sub (Ω := Ω) Δ F.Γ σ)

def reindexedPathTyping : Tm (Ω := Ω) Δ (F.reindex hσ).pathType (subTm p σ) :=
  (hp.substitute hσ).convert (F.xTyping.identitySub F.yTyping hσ)

def valueReindex : Equal (Ω := Ω) (subTm (F.value p) σ) ((F.reindex hσ).value (subTm p σ)) := by
  have hpu := Tm.transport F.familyFormation F.xTyping F.yTyping hp F.uTyping
  have ep := Tm.transportSub F.familyFormation F.xTyping F.yTyping hp F.uTyping hσ
  have ev := (Tm.transportSub F.familyFormation F.yTyping F.zTyping F.qTyping hpu hσ).transitive
    (Equal.transport (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) ep)
  exact ((Equal.subTm (F.valueAtPath hp) (.reflexive σ)).transitive ev).transitive
    ((F.reindex hσ).valueAtPath (F.reindexedPathTyping hp hσ)).symmetric

def compositeValueReindex : Equal (Ω := Ω) (subTm (F.compositeValue p) σ)
    ((F.reindex hσ).compositeValue (subTm p σ)) := by
  have ec := F.xTyping.concatSub F.yTyping F.zTyping hp F.qTyping hσ
  have ev := (Tm.transportSub F.familyFormation F.xTyping F.zTyping
    (F.xTyping.concat F.yTyping F.zTyping hp F.qTyping) F.uTyping hσ).transitive
      (Equal.transport (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) ec (.reflexive _))
  exact ((Equal.subTm (F.compositeValueAtPath hp) (.reflexive σ)).transitive ev).transitive
    ((F.reindex hσ).compositeValueAtPath (F.reindexedPathTyping hp hσ)).symmetric

def certificateReindex : Equal (Ω := Ω) (subTm (F.certificate p) σ)
    ((F.reindex hσ).certificate (subTm p σ)) :=
  (((Equal.subTm (F.certificateAtPath hp) (.reflexive σ)).transitive
    (Tm.etaSub F.familyFormation F.xTyping F.yTyping hp F.uTyping hσ F.zTyping F.qTyping)).transitive
      ((F.reindex hσ).certificateAtPath (F.reindexedPathTyping hp hσ)).symmetric)

def fiberReindex : Equal (Ω := Ω) (subTy (F.fiber p) σ) ((F.reindex hσ).fiber (subTm p σ)) :=
  (((Equal.subTy (F.fiberAtPath hp) (.reflexive σ)).transitive
    (F.familyFormation.sectionLift hσ F.zTyping).symmetric).transitive
      ((F.reindex hσ).fiberAtPath (F.reindexedPathTyping hp hσ)).symmetric)

def certificateTypeReindex : Equal (Ω := Ω) (subTy (F.certificateType p) σ)
    ((F.reindex hσ).certificateType (subTm p σ)) :=
  ((((Equal.subTy (F.certificateTypeNormalization hp) (.reflexive σ)).transitive
    ((F.valueTyping hp).identitySub (F.varyingCompositeValueTyping.substitute hp.section) hσ)).transitive
      (Equal.identity (F.fiberReindex hp hσ) (F.valueReindex hp hσ) (F.compositeValueReindex hp hσ))).transitive
        ((F.reindex hσ).certificateTypeNormalization (F.reindexedPathTyping hp hσ)).symmetric)

variable {p' h : Expression V} (hp' : Tm (Ω := Ω) F.Γ F.pathType p')
  (hh : Tm (Ω := Ω) F.Γ (identity F.pathType p p') h)

/-- Reindexing dependent action uses the pulled-back actual section; no
endpoint-only replacement or equality reflection enters the derivation. -/
def dependentActionReindex : Equal (Ω := Ω) (subTm (F.dependentAction p p' h) σ)
    (apd Δ (subTy F.pathType σ) (subTy F.certificateFamily (lift Δ F.pathType σ))
      (subTm p σ) (subTm p' σ) (subTm h σ) (subTm F.certificateSection (lift Δ F.pathType σ))) :=
  Tm.apdSub F.certificateSectionTyping hp hσ hp' hh

def dependentActionSourceReindex : Equal (Ω := Ω) (subTm (F.transportedCertificate p p' h) σ)
    (transport Δ (subTy F.pathType σ) (subTy F.certificateFamily (lift Δ F.pathType σ))
      (subTm p σ) (subTm p' σ) (subTm h σ)
      (subTm (subTm F.certificateSection (lift Δ F.pathType σ)) (sectionSub Δ (subTy F.pathType σ) (subTm p σ)))) :=
  Tm.apdSourceSub F.certificateSectionTyping hp hσ hp' hh

end
end SquareKit.Internal.DependentJudgments.Contextual.Memo.Parameters
