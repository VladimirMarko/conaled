import SquareKit.Internal.DependentJudgments.MemoReindexing

/-! Reconstruct the varying certificate section after object reindexing, then
compare the generated dependent action with the freshly reconstructed action. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Memo.Parameters
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {V : Type} {Ω : List (Judgment V)} (F : Parameters Ω)
variable {Δ σ : Expression V} (hσ : Sub (Ω := Ω) Δ F.Γ σ)

private def pathTypeReindex := F.xTyping.identitySub F.yTyping hσ

private def pathLift : Sub (Ω := Ω) (F.reindex hσ).pathContext F.pathContext (lift Δ F.pathType σ) :=
  (hσ.lift F.pathTypeFormation).resource (Equal.extend (.reflexive Δ) (F.pathTypeReindex hσ))

private def pathLiftSquare : Equal (Ω := Ω)
    (comp F.pathProjection (lift Δ F.pathType σ))
    (comp σ (F.reindex hσ).pathProjection) :=
  (hσ.liftWeaken F.pathTypeFormation).transitive
    (Equal.comp (.reflexive σ) (Equal.weaken (.reflexive Δ) (F.pathTypeReindex hσ)))

private def varyingTermReindex {A t : Expression V} (ht : Tm (Ω := Ω) F.Γ A t) :
    Equal (Ω := Ω) (subTm (subTm t F.pathProjection) (lift Δ F.pathType σ))
      (subTm (subTm t σ) (F.reindex hσ).pathProjection) :=
  ((ht.subComp F.pathTypeFormation.weaken (F.pathLift hσ)).transitive
    (Equal.subTm (.reflexive t) (F.pathLiftSquare hσ))).transitive
      (ht.subComp hσ (F.reindex hσ).pathTypeFormation.weaken).symmetric

private def varyingTypeReindex : Equal (Ω := Ω)
    (subTy F.varying.A (lift Δ F.pathType σ)) (F.reindex hσ).varying.A :=
  ((F.xTyping.family.subComp F.pathTypeFormation.weaken (F.pathLift hσ)).transitive
    (Equal.subTy (.reflexive F.A) (F.pathLiftSquare hσ))).transitive
      (F.xTyping.family.subComp hσ (F.reindex hσ).pathTypeFormation.weaken).symmetric

private def varyingDisplayReindex : Equal (Ω := Ω)
    (subTy F.varying.B (lift (F.reindex hσ).pathContext F.varying.A (lift Δ F.pathType σ)))
    (F.reindex hσ).varying.B := by
  have hπ := F.pathTypeFormation.weaken
  have hπ' := (F.reindex hσ).pathTypeFormation.weaken
  have hL := F.pathLift hσ
  have e := ((hπ.liftComp hL F.xTyping.family).transitive
    (Equal.lift (.reflexive _) (.reflexive _) (F.pathLiftSquare hσ))).transitive
      (hσ.liftComp hπ' F.xTyping.family).symmetric
  exact ((F.familyFormation.subComp (hπ.lift F.xTyping.family) (hL.lift F.varying.xTyping.family)).transitive
    (Equal.subTy (.reflexive F.B) e)).transitive
      (F.familyFormation.subComp (hσ.lift F.xTyping.family) (hπ'.lift (F.xTyping.family.substitute hσ))).symmetric

private def variablePathReindex : Equal (Ω := Ω)
    (subTm F.variablePath (lift Δ F.pathType σ)) (F.reindex hσ).variablePath :=
  (hσ.liftGeneric F.pathTypeFormation).transitive
    (Equal.generic (.reflexive Δ) (F.pathTypeReindex hσ))

/-- The selected eta section is reconstructed after lifting the substitution
through the varying path binder. -/
def certificateSectionReindex : Equal (Ω := Ω)
    (subTm F.certificateSection (lift Δ F.pathType σ)) (F.reindex hσ).certificateSection :=
  (Tm.etaSub F.varying.familyFormation F.varying.xTyping F.varying.yTyping F.variablePathTyping
    F.varying.uTyping (F.pathLift hσ) F.varying.zTyping F.varying.qTyping).transitive
      (Equal.eta (.reflexive _) (F.varyingTypeReindex hσ) (F.varyingDisplayReindex hσ)
        (F.varyingTermReindex hσ F.xTyping) (F.varyingTermReindex hσ F.yTyping)
        (F.varyingTermReindex hσ F.zTyping) (F.variablePathReindex hσ)
        (F.varyingTermReindex hσ F.qTyping) (F.varyingTermReindex hσ F.uTyping))

private def varyingValueReindex : Equal (Ω := Ω)
    (subTm F.varyingValue (lift Δ F.pathType σ)) (F.reindex hσ).varyingValue := by
  have inner := Tm.transport F.varying.familyFormation F.varying.xTyping F.varying.yTyping F.variablePathTyping F.varying.uTyping
  have ei := (Tm.transportSub F.varying.familyFormation F.varying.xTyping F.varying.yTyping F.variablePathTyping
    F.varying.uTyping (F.pathLift hσ)).transitive
      (Equal.transport (.reflexive _) (F.varyingTypeReindex hσ) (F.varyingDisplayReindex hσ)
        (F.varyingTermReindex hσ F.xTyping) (F.varyingTermReindex hσ F.yTyping)
        (F.variablePathReindex hσ) (F.varyingTermReindex hσ F.uTyping))
  exact (Tm.transportSub F.varying.familyFormation F.varying.yTyping F.varying.zTyping F.varying.qTyping
    inner (F.pathLift hσ)).transitive
      (Equal.transport (.reflexive _) (F.varyingTypeReindex hσ) (F.varyingDisplayReindex hσ)
        (F.varyingTermReindex hσ F.yTyping) (F.varyingTermReindex hσ F.zTyping)
        (F.varyingTermReindex hσ F.qTyping) ei)

private def varyingCompositeValueReindex : Equal (Ω := Ω)
    (subTm F.varyingCompositeValue (lift Δ F.pathType σ)) (F.reindex hσ).varyingCompositeValue := by
  have hc := F.varying.xTyping.concat F.varying.yTyping F.varying.zTyping F.variablePathTyping F.varying.qTyping
  have ec := (F.varying.xTyping.concatSub F.varying.yTyping F.varying.zTyping F.variablePathTyping
    F.varying.qTyping (F.pathLift hσ)).transitive
      (Equal.concat (.reflexive _) (F.varyingTypeReindex hσ)
        (F.varyingTermReindex hσ F.xTyping) (F.varyingTermReindex hσ F.yTyping)
        (F.varyingTermReindex hσ F.zTyping) (F.variablePathReindex hσ) (F.varyingTermReindex hσ F.qTyping))
  exact (Tm.transportSub F.varying.familyFormation F.varying.xTyping F.varying.zTyping hc F.varying.uTyping (F.pathLift hσ)).transitive
    (Equal.transport (.reflexive _) (F.varyingTypeReindex hσ) (F.varyingDisplayReindex hσ)
      (F.varyingTermReindex hσ F.xTyping) (F.varyingTermReindex hσ F.zTyping)
      ec (F.varyingTermReindex hσ F.uTyping))

private def varyingFiberReindex : Equal (Ω := Ω)
    (subTy F.varyingFiber (lift Δ F.pathType σ)) (F.reindex hσ).varyingFiber :=
  (F.varying.familyFormation.sectionLift (F.pathLift hσ) F.varying.zTyping).symmetric.transitive
    (Equal.subTy (F.varyingDisplayReindex hσ)
      (Equal.sectionSub (.reflexive _) (F.varyingTypeReindex hσ) (F.varyingTermReindex hσ F.zTyping)))

/-- The entire certificate family, including both value-dependent endpoints,
is reconstructed under the lifted context arrow. -/
def certificateFamilyReindex : Equal (Ω := Ω)
    (subTy F.certificateFamily (lift Δ F.pathType σ)) (F.reindex hσ).certificateFamily :=
  (F.varyingValueTyping.identitySub F.varyingCompositeValueTyping (F.pathLift hσ)).transitive
    (Equal.identity (F.varyingFiberReindex hσ) (F.varyingValueReindex hσ) (F.varyingCompositeValueReindex hσ))

private def apdCongr {A A' B B' t t' x y p : Expression V}
    (eA : Equal (Ω := Ω) A A') (eB : Equal (Ω := Ω) B B') (et : Equal (Ω := Ω) t t') :
    Equal (Ω := Ω) (apd Δ A B x y p t) (apd Δ A' B' x y p t') := by
  have e := Equal.recipe (Ω := Ω)
    (apd (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6) : Expression (Fin 7))
    ![Δ,A,B,x,y,p,t] ![Δ,A',B',x,y,p,t']
    (Fin.cases (.reflexive Δ) (Fin.cases eA (Fin.cases eB (Fin.cases (.reflexive x)
      (Fin.cases (.reflexive y) (Fin.cases (.reflexive p) (Fin.cases et (fun i => nomatch i))))))))
  simpa [apd, apdMotive, apdBranch, transportGeneric, transportMotive, basedJ, endpoint, pathFamily, sectionSub] using e

variable {p p' h : Expression V} (hp : Tm (Ω := Ω) F.Γ F.pathType p)
  (hp' : Tm (Ω := Ω) F.Γ F.pathType p')
  (hh : Tm (Ω := Ω) F.Γ (identity F.pathType p p') h)

/-- Fresh reconstruction preserves the chosen dependent action, including
its constructed varying family and chosen eta section. -/
def dependentActionFresh : Equal (Ω := Ω) (subTm (F.dependentAction p p' h) σ)
    ((F.reindex hσ).dependentAction (subTm p σ) (subTm p' σ) (subTm h σ)) :=
  (F.dependentActionReindex hp hσ hp' hh).transitive
    (apdCongr (F.pathTypeReindex hσ) (F.certificateFamilyReindex hσ) (F.certificateSectionReindex hσ))

/-- The transported source also agrees with fresh reconstruction. -/
def transportedCertificateFresh : Equal (Ω := Ω) (subTm (F.transportedCertificate p p' h) σ)
    ((F.reindex hσ).transportedCertificate (subTm p σ) (subTm p' σ) (subTm h σ)) :=
  (Tm.transportSub F.certificateSectionTyping.family hp hp' hh (F.certificateTyping hp) hσ).transitive
    (Equal.transport (.reflexive Δ) (F.pathTypeReindex hσ) (F.certificateFamilyReindex hσ)
      (.reflexive _) (.reflexive _) (.reflexive _) (F.certificateReindex hp hσ))

end
end SquareKit.Internal.DependentJudgments.Contextual.Memo.Parameters
