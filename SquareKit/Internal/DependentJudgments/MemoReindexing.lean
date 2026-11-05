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

def reindexedPath_typed : Tm (Ω := Ω) Δ (F.reindex hσ).pathType (subTm p σ) :=
  (hp.substitute hσ).convert (F.x_typed.identitySub F.y_typed hσ)

def value_reindex : Equal (Ω := Ω) (subTm (F.value p) σ) ((F.reindex hσ).value (subTm p σ)) := by
  have hpu := Tm.transport F.B_typed F.x_typed F.y_typed hp F.u_typed
  have ep := Tm.transportSub F.B_typed F.x_typed F.y_typed hp F.u_typed hσ
  have ev := (Tm.transportSub F.B_typed F.y_typed F.z_typed F.q_typed hpu hσ).transitive
    (Equal.transport (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) ep)
  exact ((Equal.subTm (F.value_atPath hp) (.reflexive σ)).transitive ev).transitive
    ((F.reindex hσ).value_atPath (F.reindexedPath_typed hp hσ)).symmetric

def compositeValue_reindex : Equal (Ω := Ω) (subTm (F.compositeValue p) σ)
    ((F.reindex hσ).compositeValue (subTm p σ)) := by
  have ec := F.x_typed.concatSub F.y_typed F.z_typed hp F.q_typed hσ
  have ev := (Tm.transportSub F.B_typed F.x_typed F.z_typed
    (F.x_typed.concat F.y_typed F.z_typed hp F.q_typed) F.u_typed hσ).transitive
      (Equal.transport (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) ec (.reflexive _))
  exact ((Equal.subTm (F.compositeValue_atPath hp) (.reflexive σ)).transitive ev).transitive
    ((F.reindex hσ).compositeValue_atPath (F.reindexedPath_typed hp hσ)).symmetric

def certificate_reindex : Equal (Ω := Ω) (subTm (F.certificate p) σ)
    ((F.reindex hσ).certificate (subTm p σ)) :=
  (((Equal.subTm (F.certificate_atPath hp) (.reflexive σ)).transitive
    (Tm.etaSub F.B_typed F.x_typed F.y_typed hp F.u_typed hσ F.z_typed F.q_typed)).transitive
      ((F.reindex hσ).certificate_atPath (F.reindexedPath_typed hp hσ)).symmetric)

def fiber_reindex : Equal (Ω := Ω) (subTy (F.fiber p) σ) ((F.reindex hσ).fiber (subTm p σ)) :=
  (((Equal.subTy (F.fiber_atPath hp) (.reflexive σ)).transitive
    (F.B_typed.sectionLift hσ F.z_typed).symmetric).transitive
      ((F.reindex hσ).fiber_atPath (F.reindexedPath_typed hp hσ)).symmetric)

def certificateType_reindex : Equal (Ω := Ω) (subTy (F.certificateType p) σ)
    ((F.reindex hσ).certificateType (subTm p σ)) :=
  ((((Equal.subTy (F.certificateType_eq hp) (.reflexive σ)).transitive
    ((F.value_typed hp).identitySub (F.varyingCompositeValue_typed.substitute hp.section) hσ)).transitive
      (Equal.identity (F.fiber_reindex hp hσ) (F.value_reindex hp hσ) (F.compositeValue_reindex hp hσ))).transitive
        ((F.reindex hσ).certificateType_eq (F.reindexedPath_typed hp hσ)).symmetric)

variable {p' h : Expression V} (hp' : Tm (Ω := Ω) F.Γ F.pathType p')
  (hh : Tm (Ω := Ω) F.Γ (identity F.pathType p p') h)

/-- Reindexing dependent action uses the pulled-back actual section; no
endpoint-only replacement or equality reflection enters the derivation. -/
def dependentAction_reindex : Equal (Ω := Ω) (subTm (F.dependentAction p p' h) σ)
    (apd Δ (subTy F.pathType σ) (subTy F.certificateFamily (lift Δ F.pathType σ))
      (subTm p σ) (subTm p' σ) (subTm h σ) (subTm F.certificateSection (lift Δ F.pathType σ))) :=
  Tm.apdSub F.certificateSection_typed hp hσ hp' hh

def dependentActionSource_reindex : Equal (Ω := Ω) (subTm (F.transportedCertificate p p' h) σ)
    (transport Δ (subTy F.pathType σ) (subTy F.certificateFamily (lift Δ F.pathType σ))
      (subTm p σ) (subTm p' σ) (subTm h σ)
      (subTm (subTm F.certificateSection (lift Δ F.pathType σ)) (sectionSub Δ (subTy F.pathType σ) (subTm p σ)))) :=
  Tm.apdSourceSub F.certificateSection_typed hp hσ hp' hh

end
end SquareKit.Internal.DependentJudgments.Contextual.Memo.Parameters
