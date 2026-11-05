import SquareKit.Internal.DependentJudgments.MemoReindexing

/-! Reconstruct the varying certificate section after object reindexing, then
compare the generated dependent action with the freshly reconstructed action. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Memo.Parameters
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {V : Type} {Ω : List (Judgment V)} (F : Parameters Ω)
variable {Δ σ : Expression V} (hσ : Sub (Ω := Ω) Δ F.Γ σ)

private def pathType_reindex := F.x_typed.identitySub F.y_typed hσ

private def pathLift : Sub (Ω := Ω) (F.reindex hσ).pathContext F.pathContext (lift Δ F.pathType σ) :=
  (hσ.lift F.pathType_typed).resource (Equal.extend (.reflexive Δ) (F.pathType_reindex hσ))

private def pathLift_square : Equal (Ω := Ω)
    (comp F.pathProjection (lift Δ F.pathType σ))
    (comp σ (F.reindex hσ).pathProjection) :=
  (hσ.liftWeaken F.pathType_typed).transitive
    (Equal.comp (.reflexive σ) (Equal.weaken (.reflexive Δ) (F.pathType_reindex hσ)))

private def varyingTerm_reindex {A t : Expression V} (ht : Tm (Ω := Ω) F.Γ A t) :
    Equal (Ω := Ω) (subTm (subTm t F.pathProjection) (lift Δ F.pathType σ))
      (subTm (subTm t σ) (F.reindex hσ).pathProjection) :=
  ((ht.subComp F.pathType_typed.weaken (F.pathLift hσ)).transitive
    (Equal.subTm (.reflexive t) (F.pathLift_square hσ))).transitive
      (ht.subComp hσ (F.reindex hσ).pathType_typed.weaken).symmetric

private def varyingType_reindex : Equal (Ω := Ω)
    (subTy F.varying.A (lift Δ F.pathType σ)) (F.reindex hσ).varying.A :=
  ((F.x_typed.family.subComp F.pathType_typed.weaken (F.pathLift hσ)).transitive
    (Equal.subTy (.reflexive F.A) (F.pathLift_square hσ))).transitive
      (F.x_typed.family.subComp hσ (F.reindex hσ).pathType_typed.weaken).symmetric

private def varyingDisplay_reindex : Equal (Ω := Ω)
    (subTy F.varying.B (lift (F.reindex hσ).pathContext F.varying.A (lift Δ F.pathType σ)))
    (F.reindex hσ).varying.B := by
  have hπ := F.pathType_typed.weaken
  have hπ' := (F.reindex hσ).pathType_typed.weaken
  have hL := F.pathLift hσ
  have e := ((hπ.liftComp hL F.x_typed.family).transitive
    (Equal.lift (.reflexive _) (.reflexive _) (F.pathLift_square hσ))).transitive
      (hσ.liftComp hπ' F.x_typed.family).symmetric
  exact ((F.B_typed.subComp (hπ.lift F.x_typed.family) (hL.lift F.varying.x_typed.family)).transitive
    (Equal.subTy (.reflexive F.B) e)).transitive
      (F.B_typed.subComp (hσ.lift F.x_typed.family) (hπ'.lift (F.x_typed.family.substitute hσ))).symmetric

private def variablePath_reindex : Equal (Ω := Ω)
    (subTm F.variablePath (lift Δ F.pathType σ)) (F.reindex hσ).variablePath :=
  (hσ.liftGeneric F.pathType_typed).transitive
    (Equal.generic (.reflexive Δ) (F.pathType_reindex hσ))

/-- The selected eta section is reconstructed after lifting the substitution
through the varying path binder. -/
def certificateSection_reindex : Equal (Ω := Ω)
    (subTm F.certificateSection (lift Δ F.pathType σ)) (F.reindex hσ).certificateSection :=
  (Tm.etaSub F.varying.B_typed F.varying.x_typed F.varying.y_typed F.variablePath_typed
    F.varying.u_typed (F.pathLift hσ) F.varying.z_typed F.varying.q_typed).transitive
      (Equal.eta (.reflexive _) (F.varyingType_reindex hσ) (F.varyingDisplay_reindex hσ)
        (F.varyingTerm_reindex hσ F.x_typed) (F.varyingTerm_reindex hσ F.y_typed)
        (F.varyingTerm_reindex hσ F.z_typed) (F.variablePath_reindex hσ)
        (F.varyingTerm_reindex hσ F.q_typed) (F.varyingTerm_reindex hσ F.u_typed))

private def varyingValue_reindex : Equal (Ω := Ω)
    (subTm F.varyingValue (lift Δ F.pathType σ)) (F.reindex hσ).varyingValue := by
  have inner := Tm.transport F.varying.B_typed F.varying.x_typed F.varying.y_typed F.variablePath_typed F.varying.u_typed
  have ei := (Tm.transportSub F.varying.B_typed F.varying.x_typed F.varying.y_typed F.variablePath_typed
    F.varying.u_typed (F.pathLift hσ)).transitive
      (Equal.transport (.reflexive _) (F.varyingType_reindex hσ) (F.varyingDisplay_reindex hσ)
        (F.varyingTerm_reindex hσ F.x_typed) (F.varyingTerm_reindex hσ F.y_typed)
        (F.variablePath_reindex hσ) (F.varyingTerm_reindex hσ F.u_typed))
  exact (Tm.transportSub F.varying.B_typed F.varying.y_typed F.varying.z_typed F.varying.q_typed
    inner (F.pathLift hσ)).transitive
      (Equal.transport (.reflexive _) (F.varyingType_reindex hσ) (F.varyingDisplay_reindex hσ)
        (F.varyingTerm_reindex hσ F.y_typed) (F.varyingTerm_reindex hσ F.z_typed)
        (F.varyingTerm_reindex hσ F.q_typed) ei)

private def varyingCompositeValue_reindex : Equal (Ω := Ω)
    (subTm F.varyingCompositeValue (lift Δ F.pathType σ)) (F.reindex hσ).varyingCompositeValue := by
  have hc := F.varying.x_typed.concat F.varying.y_typed F.varying.z_typed F.variablePath_typed F.varying.q_typed
  have ec := (F.varying.x_typed.concatSub F.varying.y_typed F.varying.z_typed F.variablePath_typed
    F.varying.q_typed (F.pathLift hσ)).transitive
      (Equal.concat (.reflexive _) (F.varyingType_reindex hσ)
        (F.varyingTerm_reindex hσ F.x_typed) (F.varyingTerm_reindex hσ F.y_typed)
        (F.varyingTerm_reindex hσ F.z_typed) (F.variablePath_reindex hσ) (F.varyingTerm_reindex hσ F.q_typed))
  exact (Tm.transportSub F.varying.B_typed F.varying.x_typed F.varying.z_typed hc F.varying.u_typed (F.pathLift hσ)).transitive
    (Equal.transport (.reflexive _) (F.varyingType_reindex hσ) (F.varyingDisplay_reindex hσ)
      (F.varyingTerm_reindex hσ F.x_typed) (F.varyingTerm_reindex hσ F.z_typed)
      ec (F.varyingTerm_reindex hσ F.u_typed))

private def varyingFiber_reindex : Equal (Ω := Ω)
    (subTy F.varyingFiber (lift Δ F.pathType σ)) (F.reindex hσ).varyingFiber :=
  (F.varying.B_typed.sectionLift (F.pathLift hσ) F.varying.z_typed).symmetric.transitive
    (Equal.subTy (F.varyingDisplay_reindex hσ)
      (Equal.sectionSub (.reflexive _) (F.varyingType_reindex hσ) (F.varyingTerm_reindex hσ F.z_typed)))

/-- The entire certificate family, including both value-dependent endpoints,
is reconstructed under the lifted context arrow. -/
def certificateFamily_reindex : Equal (Ω := Ω)
    (subTy F.certificateFamily (lift Δ F.pathType σ)) (F.reindex hσ).certificateFamily :=
  (F.varyingValue_typed.identitySub F.varyingCompositeValue_typed (F.pathLift hσ)).transitive
    (Equal.identity (F.varyingFiber_reindex hσ) (F.varyingValue_reindex hσ) (F.varyingCompositeValue_reindex hσ))

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
def dependentAction_fresh : Equal (Ω := Ω) (subTm (F.dependentAction p p' h) σ)
    ((F.reindex hσ).dependentAction (subTm p σ) (subTm p' σ) (subTm h σ)) :=
  (F.dependentAction_reindex hp hσ hp' hh).transitive
    (apdCongr (F.pathType_reindex hσ) (F.certificateFamily_reindex hσ) (F.certificateSection_reindex hσ))

/-- The transported source also agrees with fresh reconstruction. -/
def transportedCertificate_fresh : Equal (Ω := Ω) (subTm (F.transportedCertificate p p' h) σ)
    ((F.reindex hσ).transportedCertificate (subTm p σ) (subTm p' σ) (subTm h σ)) :=
  (Tm.transportSub F.certificateSection_typed.family hp hp' hh (F.certificate_typed hp) hσ).transitive
    (Equal.transport (.reflexive Δ) (F.pathType_reindex hσ) (F.certificateFamily_reindex hσ)
      (.reflexive _) (.reflexive _) (.reflexive _) (F.certificate_reindex hp hσ))

end
end SquareKit.Internal.DependentJudgments.Contextual.Memo.Parameters
