import SquareKit.Internal.DependentJudgments.ReferenceCongruence
import SquareKit.Internal.DependentJudgments.DerivedPaths

/-! Typed path recipes derived inside the independent reference calculus. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory
variable {V : Type} {Ξ : List (Declaration V)}
variable {Γ Δ A B x y p t s σ τ : Expression V}
namespace Derives
noncomputable section

def sectionMap (hx : Derives Ξ (.has (.tm Γ A) x)) :
    Derives Ξ (.has (.sub Γ (Contextual.extend Γ A)) (Contextual.sectionSub Γ A x)) :=
  .pair hx.termFamily (.identitySub hx.termFamily.typeContext)
    (.convert hx (.eqSymm (.subTyId hx.termFamily)))

def pathFamily (hx : Derives Ξ (.has (.tm Γ A) x)) :
    Derives Ξ (.has (.ty (Contextual.extend Γ A)) (Contextual.pathFamily Γ A x)) :=
  .identity (.subTm hx (.weaken hx.termFamily)) (.generic hx.termFamily)

def pathProjection (hx : Derives Ξ (.has (.tm Γ A) x)) :
    Derives Ξ (.has (.sub (Contextual.path A x) (Contextual.extend Γ A))
      (Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x))) :=
  .contextConvertSub (.weaken (pathFamily hx)) (.eqSymm (.pathDef hx))
    (.eqRefl (.extend hx.termFamily))

def sectionWeaken (hx : Derives Ξ (.has (.tm Γ A) x)) :
    Derives Ξ (.eq (.sub Γ Γ)
      (Contextual.comp (Contextual.weaken Γ A) (Contextual.sectionSub Γ A x))
      (Contextual.identitySub Γ)) :=
  .weakenPair hx.termFamily (.identitySub hx.termFamily.typeContext)
    (.convert hx (.eqSymm (.subTyId hx.termFamily)))

/-- Change only the recorded common term boundary, using already derived
formation of both endpoints and the calculus's typed congruence rule. -/
def termEqualityAt (e : Derives Ξ (.eq (.tm Γ A) s t))
    (hs : Derives Ξ (.has (.tm Γ B) s)) (ht : Derives Ξ (.has (.tm Γ B) t)) :
    Derives Ξ (.eq (.tm Γ B) s t) := by
  have hi := Derives.identitySub hs.termFamily.typeContext
  have hl := Derives.convert (.subTm hs hi) (.subTyId hs.termFamily)
  have hr := Derives.convert (.subTm ht hi) (.subTyId ht.termFamily)
  have ec : Derives Ξ (.eq (.tm Γ B)
      (Contextual.subTm s (Contextual.identitySub Γ))
      (Contextual.subTm t (Contextual.identitySub Γ))) :=
    .congruence (.inl .subTm) ![.tm Γ A,.sub Γ Γ] hl hr
      (Fin.cases e (Fin.cases (.eqRefl hi) (fun i => nomatch i)))
  exact .eqTrans (.eqSymm (.subTmId hs)) (.eqTrans ec (.subTmId ht))

def subTmCongruence (ht : Derives Ξ (.has (.tm Γ A) t))
    (e : Derives Ξ (.eq (.sub Δ Γ) σ τ)) :
    Derives Ξ (.eq (.tm Δ (Contextual.subTy A σ))
      (Contextual.subTm t σ) (Contextual.subTm t τ)) :=
  .congruence (.inl .subTm) ![.tm Γ A,.sub Δ Γ]
    (.subTm ht e.eqOperands.1)
    (.convert (.subTm ht e.eqOperands.2) (.eqSymm (subTyCongruence ht.termFamily e)))
    (Fin.cases (.eqRefl ht) (Fin.cases e (fun i => nomatch i)))

def weakenSectionType (hB : Derives Ξ (.has (.ty Γ) B))
    (hx : Derives Ξ (.has (.tm Γ A) x)) :
    Derives Ξ (.eq (.ty Γ)
      (Contextual.subTy (Contextual.subTy B (Contextual.weaken Γ A)) (Contextual.sectionSub Γ A x)) B) :=
  .eqTrans (.subTyComp hB (.weaken hx.termFamily) (sectionMap hx))
    (.eqTrans (subTyCongruence hB (sectionWeaken hx)) (.subTyId hB))

def weakenSectionTerm (ht : Derives Ξ (.has (.tm Γ B) t))
    (hx : Derives Ξ (.has (.tm Γ A) x)) :
    Derives Ξ (.eq (.tm Γ B)
      (Contextual.subTm (Contextual.subTm t (Contextual.weaken Γ A)) (Contextual.sectionSub Γ A x)) t) := by
  have hl := Derives.convert (.subTm (.subTm ht (.weaken hx.termFamily)) (sectionMap hx))
    (weakenSectionType ht.termFamily hx)
  have hm := Derives.convert (.subTm ht (.comp (.weaken hx.termFamily) (sectionMap hx)))
    (.eqTrans (subTyCongruence ht.termFamily (sectionWeaken hx)) (.subTyId ht.termFamily))
  have hr := Derives.convert (.subTm ht (.identitySub ht.termFamily.typeContext)) (.subTyId ht.termFamily)
  exact .eqTrans (termEqualityAt (.subTmComp ht (.weaken hx.termFamily) (sectionMap hx)) hl hm)
    (.eqTrans (termEqualityAt (subTmCongruence ht (sectionWeaken hx)) hm hr) (.subTmId ht))

def sectionGeneric (hx : Derives Ξ (.has (.tm Γ A) x)) :
    Derives Ξ (.eq (.tm Γ A)
      (Contextual.subTm (Contextual.generic Γ A) (Contextual.sectionSub Γ A x)) x) := by
  have h := genericPairBeta hx.termFamily (.identitySub hx.termFamily.typeContext)
    (.convert hx (.eqSymm (.subTyId hx.termFamily)))
  exact termEqualityAt h
    (.convert (.subTm (.generic hx.termFamily) (sectionMap hx))
      (weakenSectionType hx.termFamily hx)) hx

def pathFamilySection (hx : Derives Ξ (.has (.tm Γ A) x))
    (hy : Derives Ξ (.has (.tm Γ A) y)) :
    Derives Ξ (.eq (.ty Γ)
      (Contextual.subTy (Contextual.pathFamily Γ A x) (Contextual.sectionSub Γ A y))
      (Contextual.identity A x y)) := by
  have e := Derives.identitySubLaw (.subTm hx (.weaken hx.termFamily))
    (.generic hx.termFamily) (sectionMap hy)
  apply Derives.eqTrans e
  exact .congruence (.inr .identity) ![.ty Γ,.tm Γ A,.tm Γ A]
    e.eqOperands.2 (.identity hx hy)
    (Fin.cases (weakenSectionType hx.termFamily hy)
      (Fin.cases (weakenSectionTerm hx hy) (Fin.cases (sectionGeneric hy) (fun i => nomatch i))))

def endpoint (hx : Derives Ξ (.has (.tm Γ A) x))
    (hy : Derives Ξ (.has (.tm Γ A) y))
    (hp : Derives Ξ (.has (.tm Γ (Contextual.identity A x y)) p)) :
    Derives Ξ (.has (.sub Γ (Contextual.path A x)) (Contextual.endpoint Γ A x y p)) :=
  .contextConvertSub
    (.pair (pathFamily hx) (sectionMap hy) (.convert hp (.eqSymm (pathFamilySection hx hy))))
    (.eqRefl hx.termFamily.typeContext) (.eqSymm (.pathDef hx))

def endpointProjection (hx : Derives Ξ (.has (.tm Γ A) x))
    (hy : Derives Ξ (.has (.tm Γ A) y))
    (hp : Derives Ξ (.has (.tm Γ (Contextual.identity A x y)) p)) :
    Derives Ξ (.eq (.sub Γ (Contextual.extend Γ A))
      (Contextual.comp (Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x))
        (Contextual.endpoint Γ A x y p)) (Contextual.sectionSub Γ A y)) :=
  .weakenPair (pathFamily hx) (sectionMap hy) (.convert hp (.eqSymm (pathFamilySection hx hy)))

def rootProjection (hx : Derives Ξ (.has (.tm Γ A) x)) :
    Derives Ξ (.eq (.sub Γ (Contextual.extend Γ A))
      (Contextual.comp (Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x))
        (Contextual.root A x)) (Contextual.sectionSub Γ A x)) := by
  have e := Derives.rootDef hx (endpoint hx hx (.reflexivity hx))
  have ec : Derives Ξ (.eq (.sub Γ (Contextual.extend Γ A))
      (Contextual.comp (Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x))
        (Contextual.root A x))
      (Contextual.comp (Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x))
        (Contextual.endpoint Γ A x x (Contextual.reflexivity A x)))) :=
    .congruence (.inl .comp) ![.sub (Contextual.path A x) (Contextual.extend Γ A), .sub Γ (Contextual.path A x)]
      (.comp (pathProjection hx) (.root hx)) (.comp (pathProjection hx) e.eqOperands.2)
      (Fin.cases (.eqRefl (pathProjection hx)) (Fin.cases e (fun i => nomatch i)))
  exact .eqTrans ec (endpointProjection hx hx (.reflexivity hx))

def basedJ {D d : Expression V} (hx : Derives Ξ (.has (.tm Γ A) x))
    (hD : Derives Ξ (.has (.ty (Contextual.path A x)) D))
    (hd : Derives Ξ (.has (.tm Γ (Contextual.subTy D (Contextual.root A x))) d)) :
    Derives Ξ (.has (.tm (Contextual.path A x) D) (Contextual.basedJ A x D d)) :=
  .j hx (.nil (.path hx)) hD hd

def basedJBeta {D d : Expression V} (hx : Derives Ξ (.has (.tm Γ A) x))
    (hD : Derives Ξ (.has (.ty (Contextual.path A x)) D))
    (hd : Derives Ξ (.has (.tm Γ (Contextual.subTy D (Contextual.root A x))) d)) :
    Derives Ξ (.eq (.tm Γ (Contextual.subTy D (Contextual.root A x)))
      (Contextual.subTm (Contextual.basedJ A x D d) (Contextual.root A x)) d) :=
  jComputation hx (.nil (.path hx)) hD hd

def transportRoot (hB : Derives Ξ (.has (.ty (Contextual.extend Γ A)) B))
    (hx : Derives Ξ (.has (.tm Γ A) x)) :
    Derives Ξ (.eq (.ty Γ)
      (Contextual.subTy (Contextual.transportMotive Γ A B x) (Contextual.root A x))
      (Contextual.subTy B (Contextual.sectionSub Γ A x))) :=
  .eqTrans (.subTyComp hB (pathProjection hx) (.root hx))
    (subTyCongruence hB (rootProjection hx))

def transportEndpoint (hB : Derives Ξ (.has (.ty (Contextual.extend Γ A)) B))
    (hx : Derives Ξ (.has (.tm Γ A) x)) (hy : Derives Ξ (.has (.tm Γ A) y))
    (hp : Derives Ξ (.has (.tm Γ (Contextual.identity A x y)) p)) :
    Derives Ξ (.eq (.ty Γ)
      (Contextual.subTy (Contextual.transportMotive Γ A B x) (Contextual.endpoint Γ A x y p))
      (Contextual.subTy B (Contextual.sectionSub Γ A y))) :=
  .eqTrans (.subTyComp hB (pathProjection hx) (endpoint hx hy hp))
    (subTyCongruence hB (endpointProjection hx hy hp))

def transport {u : Expression V} (hB : Derives Ξ (.has (.ty (Contextual.extend Γ A)) B))
    (hx : Derives Ξ (.has (.tm Γ A) x)) (hy : Derives Ξ (.has (.tm Γ A) y))
    (hp : Derives Ξ (.has (.tm Γ (Contextual.identity A x y)) p))
    (hu : Derives Ξ (.has (.tm Γ (Contextual.subTy B (Contextual.sectionSub Γ A x))) u)) :
    Derives Ξ (.has (.tm Γ (Contextual.subTy B (Contextual.sectionSub Γ A y)))
      (Contextual.transport Γ A B x y p u)) :=
  .convert (.subTm (basedJ hx (.subTy hB (pathProjection hx))
    (.convert hu (.eqSymm (transportRoot hB hx)))) (endpoint hx hy hp))
    (transportEndpoint hB hx hy hp)

def subTmComposeAlong {Θ υ : Expression V}
    (ht : Derives Ξ (.has (.tm Γ A) t))
    (hs : Derives Ξ (.has (.sub Δ Γ) σ))
    (hτ : Derives Ξ (.has (.sub Θ Δ) τ))
    (e : Derives Ξ (.eq (.sub Θ Γ) (Contextual.comp σ τ) υ)) :
    Derives Ξ (.eq (.tm Θ (Contextual.subTy A υ))
      (Contextual.subTm (Contextual.subTm t σ) τ) (Contextual.subTm t υ)) := by
  have et := subTyCongruence ht.termFamily e
  have hl := Derives.convert (.subTm (.subTm ht hs) hτ)
    (.eqTrans (.subTyComp ht.termFamily hs hτ) et)
  have hm := Derives.convert (.subTm ht (.comp hs hτ)) et
  have hr := Derives.subTm ht e.eqOperands.2
  exact .eqTrans (termEqualityAt (.subTmComp ht hs hτ) hl hm)
    (termEqualityAt (subTmCongruence ht e) hm hr)

end
end Derives
end SquareKit.Internal.DependentJudgments.Contextual.Reference
