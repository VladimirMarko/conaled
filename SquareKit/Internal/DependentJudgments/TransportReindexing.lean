import SquareKit.Internal.DependentJudgments.DerivedReindexing

/-! Object-context substitution of the generated transport and concatenation
recipes. The proof reduces the constructed path map and invokes the primitive
full contextual-J substitution rule through its empty-tail specialization. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A B σ x y z p q u : Expression V}

def Sub.liftWeaken (hσ : Sub (Ω := Ω) Δ Γ σ) (hA : Ty (Ω := Ω) Γ A) :
    Equal (Ω := Ω) (Contextual.comp (Contextual.weaken Γ A) (Contextual.lift Δ A σ)) (Contextual.comp σ (Contextual.weaken Δ (Contextual.subTy A σ))) :=
  hA.weakenPair (hσ.comp (hA.substitute hσ).weaken)
    ((hA.substitute hσ).generic.convert (hA.subComp hσ (hA.substitute hσ).weaken))

def Sub.liftGeneric (hσ : Sub (Ω := Ω) Δ Γ σ) (hA : Ty (Ω := Ω) Γ A) :
    Equal (Ω := Ω) (Contextual.subTm (Contextual.generic Γ A) (Contextual.lift Δ A σ)) (Contextual.generic Δ (Contextual.subTy A σ)) :=
  hA.variablePair (hσ.comp (hA.substitute hσ).weaken)
    ((hA.substitute hσ).generic.convert (hA.subComp hσ (hA.substitute hσ).weaken))

def Tm.pathFamilyLift (hx : Tm (Ω := Ω) Γ A x) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (Contextual.subTy (Contextual.pathFamily Γ A x) (Contextual.lift Δ A σ))
      (Contextual.pathFamily Δ (Contextual.subTy A σ) (Contextual.subTm x σ)) := by
  have hf := hσ.lift hx.family
  have hw := (hx.family.substitute hσ).weaken
  exact ((hx.substitute hx.family.weaken).identitySub hx.family.generic hf).transitive
    (Equal.identity
      (((hx.family.subComp hx.family.weaken hf).transitive
        (Equal.subTy (.reflexive A) (hσ.liftWeaken hx.family))).transitive (hx.family.subComp hσ hw).symmetric)
      (((hx.subComp hx.family.weaken hf).transitive
        (Equal.subTm (.reflexive x) (hσ.liftWeaken hx.family))).transitive (hx.subComp hσ hw).symmetric)
      (hσ.liftGeneric hx.family))

def Tm.pathSubType (hx : Tm (Ω := Ω) Γ A x) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω)
      (Contextual.subTy (Contextual.pathFamily Γ A x)
        (Contextual.comp (Contextual.lift Δ A σ) (Contextual.weaken (Contextual.extend Δ (Contextual.subTy A σ)) (Contextual.pathFamily Δ (Contextual.subTy A σ) (Contextual.subTm x σ)))))
      (Contextual.subTy (Contextual.pathFamily Δ (Contextual.subTy A σ) (Contextual.subTm x σ))
        (Contextual.weaken (Contextual.extend Δ (Contextual.subTy A σ)) (Contextual.pathFamily Δ (Contextual.subTy A σ) (Contextual.subTm x σ)))) :=
  (hx.pathFamily.subComp (hσ.lift hx.family) (hx.substitute hσ).pathFamily.weaken).symmetric.transitive
    (Equal.subTy (hx.pathFamilyLift hσ) (.reflexive _))

def Tm.pathSubProjection (hx : Tm (Ω := Ω) Γ A x) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (Contextual.comp (Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x)) (Contextual.pathSub A x σ))
      (Contextual.comp (Contextual.lift Δ A σ) (Contextual.weaken (Contextual.extend Δ (Contextual.subTy A σ)) (Contextual.pathFamily Δ (Contextual.subTy A σ) (Contextual.subTm x σ)))) :=
  (Equal.comp (.reflexive _) (hx.pathSubDef hσ)).transitive
    (hx.pathFamily.weakenPair ((hσ.lift hx.family).comp (hx.substitute hσ).pathFamily.weaken)
      ((hx.substitute hσ).pathFamily.generic.convert (hx.pathSubType hσ).symmetric))

def Tm.pathSubEndpoint (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω)
      (Contextual.comp (Contextual.pathSub A x σ) (Contextual.endpoint Δ (Contextual.subTy A σ) (Contextual.subTm x σ) (Contextual.subTm y σ) (Contextual.subTm p σ)))
      (Contextual.comp (Contextual.endpoint Γ A x y p) σ) := by
  have hxs := hx.substitute hσ
  have hys := hy.substitute hσ
  have hps := (hp.substitute hσ).convert (hx.identitySub hy hσ)
  have hpoint := hxs.endpoint hys hps
  have hgen := hxs.pathFamily.generic.convert (hx.pathSubType hσ).symmetric
  have ebase := (((hσ.lift hx.family).assoc hxs.pathProjection hpoint).transitive
    (Equal.comp (.reflexive _) (hxs.endpointProjection hys hps))).transitive (hσ.liftSection hy)
  have eterm := hxs.pathFamily.variablePair hys.section (hps.convert (hxs.pathFamilySection hys).symmetric)
  have eleft := ((Equal.comp (hx.pathSubDef hσ) (.reflexive _)).transitive
    (hx.pathFamily.pairComp ((hσ.lift hx.family).comp hxs.pathProjection)
      (hgen.recontext hxs.pathDef.symmetric) hpoint)).transitive
        (Equal.pair (.reflexive _) ebase eterm)
  have eright := hx.pathFamily.pairComp hy.section (hp.convert (hx.pathFamilySection hy).symmetric) hσ
  exact eleft.transitive eright.symmetric

def Ty.transportMotiveSub (hB : Ty (Ω := Ω) (Contextual.extend Γ A) B) (hx : Tm (Ω := Ω) Γ A x)
    (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (Contextual.subTy (Contextual.transportMotive Γ A B x) (Contextual.pathSub A x σ))
      (Contextual.transportMotive Δ (Contextual.subTy A σ) (Contextual.subTy B (Contextual.lift Δ A σ)) (Contextual.subTm x σ)) :=
  ((hB.subComp hx.pathProjection (hx.pathSub hσ)).transitive
    (Equal.subTy (.reflexive B) (hx.pathSubProjection hσ))).transitive
      (hB.subComp (hσ.lift hx.family) (hx.substitute hσ).pathProjection).symmetric

def Tm.transportSub (hB : Ty (Ω := Ω) (Contextual.extend Γ A) B) (hx : Tm (Ω := Ω) Γ A x)
    (hy : Tm (Ω := Ω) Γ A y) (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p)
    (hu : Tm (Ω := Ω) Γ (Contextual.subTy B (Contextual.sectionSub Γ A x)) u) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (Contextual.subTm (Contextual.transport Γ A B x y p u) σ)
      (Contextual.transport Δ (Contextual.subTy A σ) (Contextual.subTy B (Contextual.lift Δ A σ)) (Contextual.subTm x σ) (Contextual.subTm y σ) (Contextual.subTm p σ) (Contextual.subTm u σ)) := by
  have hG := Tm.transportGeneric hB hx hu
  have hxs := hx.substitute hσ
  have hys := hy.substitute hσ
  have hps := (hp.substitute hσ).convert (hx.identitySub hy hσ)
  have he := hxs.endpoint hys hps
  have eJ := (hx.basedJSub (hB.substitute hx.pathProjection) (hu.convert (hB.transportRoot hx).symmetric) hσ).transitive
    (Equal.j (.reflexive _) (.reflexive _) (.reflexive _) (hB.transportMotiveSub hx hσ) (.reflexive _))
  exact ((hG.subComp (hx.endpoint hy hp) hσ).transitive
    (Equal.subTm (.reflexive _) (hx.pathSubEndpoint hy hp hσ).symmetric)).transitive
      (((hG.subComp (hx.pathSub hσ) he).symmetric).transitive (Equal.subTm eJ (.reflexive _)))

def Equal.transportFamily {Γ A B B' x y p u : Expression V} (hB : Equal (Ω := Ω) B B') :
    Equal (Ω := Ω) (Contextual.transport Γ A B x y p u) (Contextual.transport Γ A B' x y p u) :=
  Equal.subTm (Equal.j (.reflexive _) (.reflexive _) (.reflexive _) (Equal.subTy hB (.reflexive _)) (.reflexive _)) (.reflexive _)

def Tm.concatSub (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hz : Tm (Ω := Ω) Γ A z) (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p)
    (hq : Tm (Ω := Ω) Γ (Contextual.identity A y z) q) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (Contextual.subTm (Contextual.concat Γ A x y z p q) σ)
      (Contextual.concat Δ (Contextual.subTy A σ) (Contextual.subTm x σ) (Contextual.subTm y σ) (Contextual.subTm z σ) (Contextual.subTm p σ) (Contextual.subTm q σ)) :=
  (Tm.transportSub hx.pathFamily hy hz hq (hp.convert (hx.pathFamilySection hy).symmetric) hσ).transitive
    (Equal.transportFamily (hx.pathFamilyLift hσ))

end SquareKit.Internal.DependentJudgments.Contextual
