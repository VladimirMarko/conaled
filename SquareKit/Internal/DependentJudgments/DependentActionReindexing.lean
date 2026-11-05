import SquareKit.Internal.DependentJudgments.CertificateReindexing

/-! Dependent action under object-context substitution, with its source
transport and the varying section both reindexed through comprehension. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A B σ x y p t : Expression V}

def Tm.sectionLift (ht : Tm (Ω := Ω) (Contextual.extend Γ A) B t) (hσ : Sub (Ω := Ω) Δ Γ σ)
    (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (Contextual.subTm (Contextual.subTm t (Contextual.lift Δ A σ)) (Contextual.sectionSub Δ (Contextual.subTy A σ) (Contextual.subTm x σ)))
      (Contextual.subTm (Contextual.subTm t (Contextual.sectionSub Γ A x)) σ) :=
  ((ht.subComp (hσ.lift hx.family) (hx.substitute hσ).section).transitive
    (Equal.subTm (.reflexive t) (hσ.liftSection hx))).transitive (ht.subComp hx.section hσ).symmetric

section Apd
variable (ht : Tm (Ω := Ω) (Contextual.extend Γ A) B t) (hx : Tm (Ω := Ω) Γ A x)
  (hσ : Sub (Ω := Ω) Δ Γ σ)

def Tm.apdMotiveSub : Equal (Ω := Ω) (Contextual.subTy (Contextual.apdMotive Γ A B x t) (Contextual.pathSub A x σ))
    (Contextual.apdMotive Δ (Contextual.subTy A σ) (Contextual.subTy B (Contextual.lift Δ A σ)) (Contextual.subTm x σ) (Contextual.subTm t (Contextual.lift Δ A σ))) := by
  have hG := Tm.transportGeneric ht.family hx (ht.substitute hx.section)
  have el := (Tm.transportGenericSub ht.family hx (ht.substitute hx.section) hσ).transitive
    (Equal.transportGeneric (.reflexive _) (ht.sectionLift hσ hx).symmetric)
  have er := ((ht.subComp hx.pathProjection (hx.pathSub hσ)).transitive
    (Equal.subTm (.reflexive _) (hx.pathSubProjection hσ))).transitive
      (ht.subComp (hσ.lift hx.family) (hx.substitute hσ).pathProjection).symmetric
  exact (hG.identitySub (ht.substitute hx.pathProjection) (hx.pathSub hσ)).transitive
    (Equal.identity (ht.family.transportMotiveSub hx hσ) el er)

def Tm.apdBranchSub : Equal (Ω := Ω) (Contextual.subTm (Contextual.apdBranch Γ A B x t) σ)
    (Contextual.apdBranch Δ (Contextual.subTy A σ) (Contextual.subTy B (Contextual.lift Δ A σ)) (Contextual.subTm x σ) (Contextual.subTm t (Contextual.lift Δ A σ))) :=
  ((ht.substitute hx.section).reflSub hσ).transitive
    (Equal.reflexivity (ht.family.sectionLift hσ hx).symmetric (ht.sectionLift hσ hx).symmetric)

variable (hy : Tm (Ω := Ω) Γ A y) (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p)

def Tm.apdSub : Equal (Ω := Ω) (Contextual.subTm (Contextual.apd Γ A B x y p t) σ)
    (Contextual.apd Δ (Contextual.subTy A σ) (Contextual.subTy B (Contextual.lift Δ A σ)) (Contextual.subTm x σ) (Contextual.subTm y σ) (Contextual.subTm p σ) (Contextual.subTm t (Contextual.lift Δ A σ))) := by
  have hJ := hx.basedJ (Tm.apdMotive ht hx) (Tm.apdBranch ht hx)
  have he := (hx.substitute hσ).endpoint (hy.substitute hσ) ((hp.substitute hσ).convert (hx.identitySub hy hσ))
  have eJ := (hx.basedJSub (Tm.apdMotive ht hx) (Tm.apdBranch ht hx) hσ).transitive
    (Equal.j (.reflexive _) (.reflexive _) (.reflexive _) (Tm.apdMotiveSub ht hx hσ) (Tm.apdBranchSub ht hx hσ))
  exact ((hJ.subComp (hx.endpoint hy hp) hσ).transitive
    (Equal.subTm (.reflexive _) (hx.pathSubEndpoint hy hp hσ).symmetric)).transitive
      (((hJ.subComp (hx.pathSub hσ) he).symmetric).transitive (Equal.subTm eJ (.reflexive _)))

/-- The source of dependent action is itself transported through the same
object substitution, not replaced by an untransported endpoint. -/
def Tm.apdSourceSub : Equal (Ω := Ω)
    (Contextual.subTm (Contextual.transport Γ A B x y p (Contextual.subTm t (Contextual.sectionSub Γ A x))) σ)
    (Contextual.transport Δ (Contextual.subTy A σ) (Contextual.subTy B (Contextual.lift Δ A σ)) (Contextual.subTm x σ) (Contextual.subTm y σ) (Contextual.subTm p σ)
      (Contextual.subTm (Contextual.subTm t (Contextual.lift Δ A σ)) (Contextual.sectionSub Δ (Contextual.subTy A σ) (Contextual.subTm x σ)))) :=
  (Tm.transportSub ht.family hx hy hp (ht.substitute hx.section) hσ).transitive
    (Equal.subTm (Equal.transportGeneric (.reflexive _) (ht.sectionLift hσ hx).symmetric) (.reflexive _))

end Apd
end SquareKit.Internal.DependentJudgments.Contextual
