import SquareKit.Internal.DependentJudgments.TransportReindexing

/-! The selected composition certificate commutes with object substitution.
The proof transports its J motive and reflexive branch, not only endpoints. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A B σ x y z p q u : Expression V}

private def ruleInstance (a : Axiom) (σ : Fin (rule a).parameterCount → Expression V)
    (h : ∀ i, Derivation theory Ω (((rule a).premise i).subst σ)) :
    Derivation theory Ω ((rule a).conclusion.subst σ) :=
  Derivation.rule (T := theory) (Sum.inr a) σ h

def Tm.reflSub (hx : Tm (Ω := Ω) Γ A x) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (Contextual.subTm (Contextual.reflexivity A x) σ) (Contextual.reflexivity (Contextual.subTy A σ) (Contextual.subTm x σ)) := by
  have e := ruleInstance (Ω := Ω) .reflSub ![Γ, Δ, A, x, σ]
    (Fin.cases (by simpa [rule] using hx) (Fin.cases (by simpa [rule] using hσ) (fun i => nomatch i)))
  simpa [rule] using e

def Equal.reflexivity {A A' x x' : Expression V} (hA : Equal (Ω := Ω) A A') (hx : Equal (Ω := Ω) x x') :
    Equal (Ω := Ω) (Contextual.reflexivity A x) (Contextual.reflexivity A' x') :=
  Derivation.congruence (T := theory) (Sum.inr Operation.reflexivity)
    (Fin.cases hA (Fin.cases hx (fun i => nomatch i)))

def Equal.transportGeneric {Γ A B B' x u u' : Expression V}
    (hB : Equal (Ω := Ω) B B') (hu : Equal (Ω := Ω) u u') :
    Equal (Ω := Ω) (Contextual.transportGeneric Γ A B x u) (Contextual.transportGeneric Γ A B' x u') :=
  Equal.j (.reflexive _) (.reflexive _) (.reflexive _) (Equal.subTy hB (.reflexive _)) hu

def Tm.transportGenericSub (hB : Ty (Ω := Ω) (Contextual.extend Γ A) B) (hx : Tm (Ω := Ω) Γ A x)
    (hu : Tm (Ω := Ω) Γ (Contextual.subTy B (Contextual.sectionSub Γ A x)) u) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (Contextual.subTm (Contextual.transportGeneric Γ A B x u) (Contextual.pathSub A x σ))
      (Contextual.transportGeneric Δ (Contextual.subTy A σ) (Contextual.subTy B (Contextual.lift Δ A σ)) (Contextual.subTm x σ) (Contextual.subTm u σ)) :=
  (hx.basedJSub (hB.substitute hx.pathProjection) (hu.convert (hB.transportRoot hx).symmetric) hσ).transitive
    (Equal.j (.reflexive _) (.reflexive _) (.reflexive _) (hB.transportMotiveSub hx hσ) (.reflexive _))

def Tm.concatGenericSub (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (Contextual.subTm (Contextual.concatGeneric Γ A x y p) (Contextual.pathSub A y σ))
      (Contextual.concatGeneric Δ (Contextual.subTy A σ) (Contextual.subTm x σ) (Contextual.subTm y σ) (Contextual.subTm p σ)) :=
  (Tm.transportGenericSub hx.pathFamily hy (hp.convert (hx.pathFamilySection hy).symmetric) hσ).transitive
    (Equal.transportGeneric (hx.pathFamilyLift hσ) (.reflexive _))

def Tm.concatMapSub (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (Contextual.comp (Contextual.concatMap Γ A x y p) (Contextual.pathSub A y σ))
      (Contextual.comp (Contextual.pathSub A x σ) (Contextual.concatMap Δ (Contextual.subTy A σ) (Contextual.subTm x σ) (Contextual.subTm y σ) (Contextual.subTm p σ))) := by
  have hxs := hx.substitute hσ
  have hys := hy.substitute hσ
  have hps := (hp.substitute hσ).convert (hx.identitySub hy hσ)
  have hs := hxs.concatMap hys hps
  have left := (hx.pathFamily.pairComp hy.pathProjection (hx.concatGeneric hy hp) (hy.pathSub hσ)).transitive
    (Equal.pair (.reflexive _) (hy.pathSubProjection hσ) (hx.concatGenericSub hy hp hσ))
  have base := ((hσ.lift hx.family).assoc hxs.pathProjection hs).transitive
    (Equal.comp (.reflexive _) (hxs.concatMapProjection hys hps))
  have Contextual.generic := hxs.pathFamily.variablePair hys.pathProjection (hxs.concatGeneric hys hps)
  have right := ((Equal.comp (hx.pathSubDef hσ) (.reflexive _)).transitive
    (hx.pathFamily.pairComp ((hσ.lift hx.family).comp hxs.pathProjection)
      ((hxs.pathFamily.generic.convert (hx.pathSubType hσ).symmetric).recontext hxs.pathDef.symmetric) hs)).transitive
        (Equal.pair (.reflexive _) base Contextual.generic)
  exact left.transitive right.symmetric

section Eta
variable (hB : Ty (Ω := Ω) (Contextual.extend Γ A) B) (hx : Tm (Ω := Ω) Γ A x)
  (hy : Tm (Ω := Ω) Γ A y) (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p)
  (hu : Tm (Ω := Ω) Γ (Contextual.subTy B (Contextual.sectionSub Γ A x)) u) (hσ : Sub (Ω := Ω) Δ Γ σ)

def Tm.etaLeftSub : Equal (Ω := Ω) (Contextual.subTm (Contextual.etaLeft Γ A B x y p u) (Contextual.pathSub A y σ))
    (Contextual.etaLeft Δ (Contextual.subTy A σ) (Contextual.subTy B (Contextual.lift Δ A σ)) (Contextual.subTm x σ) (Contextual.subTm y σ) (Contextual.subTm p σ) (Contextual.subTm u σ)) :=
  (Tm.transportGenericSub hB hy (Tm.transport hB hx hy hp hu) hσ).transitive
    (Equal.transportGeneric (.reflexive _) (Tm.transportSub hB hx hy hp hu hσ))

def Tm.etaRightSub : Equal (Ω := Ω) (Contextual.subTm (Contextual.etaRight Γ A B x y p u) (Contextual.pathSub A y σ))
    (Contextual.etaRight Δ (Contextual.subTy A σ) (Contextual.subTy B (Contextual.lift Δ A σ)) (Contextual.subTm x σ) (Contextual.subTm y σ) (Contextual.subTm p σ) (Contextual.subTm u σ)) := by
  have hG := Tm.transportGeneric hB hx hu
  have hs := (hx.substitute hσ).concatMap (hy.substitute hσ) ((hp.substitute hσ).convert (hx.identitySub hy hσ))
  exact ((hG.subComp (hx.concatMap hy hp) (hy.pathSub hσ)).transitive
    (Equal.subTm (.reflexive _) (hx.concatMapSub hy hp hσ))).transitive
      (((hG.subComp (hx.pathSub hσ) hs).symmetric).transitive
        (Equal.subTm (Tm.transportGenericSub hB hx hu hσ) (.reflexive _)))

def Tm.etaMotiveSub : Equal (Ω := Ω) (Contextual.subTy (Contextual.etaMotive Γ A B x y p u) (Contextual.pathSub A y σ))
    (Contextual.etaMotive Δ (Contextual.subTy A σ) (Contextual.subTy B (Contextual.lift Δ A σ)) (Contextual.subTm x σ) (Contextual.subTm y σ) (Contextual.subTm p σ) (Contextual.subTm u σ)) :=
  ((Tm.etaLeft hB hx hy hp hu).identitySub (Tm.etaRight hB hx hy hp hu) (hy.pathSub hσ)).transitive
    (Equal.identity (hB.transportMotiveSub hy hσ) (Tm.etaLeftSub hB hx hy hp hu hσ) (Tm.etaRightSub hB hx hy hp hu hσ))

def Tm.etaBranchSub : Equal (Ω := Ω) (Contextual.subTm (Contextual.etaBranch Γ A B x y p u) σ)
    (Contextual.etaBranch Δ (Contextual.subTy A σ) (Contextual.subTy B (Contextual.lift Δ A σ)) (Contextual.subTm x σ) (Contextual.subTm y σ) (Contextual.subTm p σ) (Contextual.subTm u σ)) :=
  ((Tm.transport hB hx hy hp hu).reflSub hσ).transitive
    (Equal.reflexivity (hB.sectionLift hσ hy).symmetric (Tm.transportSub hB hx hy hp hu hσ))

variable (hz : Tm (Ω := Ω) Γ A z) (hq : Tm (Ω := Ω) Γ (Contextual.identity A y z) q)

def Tm.etaSub : Equal (Ω := Ω) (Contextual.subTm (Contextual.eta Γ A B x y z p q u) σ)
    (Contextual.eta Δ (Contextual.subTy A σ) (Contextual.subTy B (Contextual.lift Δ A σ)) (Contextual.subTm x σ) (Contextual.subTm y σ) (Contextual.subTm z σ)
      (Contextual.subTm p σ) (Contextual.subTm q σ) (Contextual.subTm u σ)) := by
  have hJ := hy.basedJ (Tm.etaMotive hB hx hy hp hu) (Tm.etaBranch hB hx hy hp hu)
  have he := (hy.substitute hσ).endpoint (hz.substitute hσ) ((hq.substitute hσ).convert (hy.identitySub hz hσ))
  have eJ := (hy.basedJSub (Tm.etaMotive hB hx hy hp hu) (Tm.etaBranch hB hx hy hp hu) hσ).transitive
    (Equal.j (.reflexive _) (.reflexive _) (.reflexive _) (Tm.etaMotiveSub hB hx hy hp hu hσ) (Tm.etaBranchSub hB hx hy hp hu hσ))
  exact ((hJ.subComp (hy.endpoint hz hq) hσ).transitive
    (Equal.subTm (.reflexive _) (hy.pathSubEndpoint hz hq hσ).symmetric)).transitive
      (((hJ.subComp (hy.pathSub hσ) he).symmetric).transitive (Equal.subTm eJ (.reflexive _)))

end Eta
end SquareKit.Internal.DependentJudgments.Contextual
