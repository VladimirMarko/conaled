import SquareKit.Internal.DependentJudgments.DerivedCertificates
/-! Ordinary action on identities derived in the source calculus using J. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ A C x y p t : Expression V}
abbrev ordinaryApply (Γ A x t : Expression V) := Contextual.subTm t (Contextual.sectionSub Γ A x)
abbrev ordinaryApLeft (Γ A x t : Expression V) :=
 Contextual.subTm (Contextual.subTm (ordinaryApply Γ A x t) (Contextual.weaken Γ A))
  (Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x))
abbrev ordinaryApMotive (Γ A C x t : Expression V) :=
 Contextual.identity (Contextual.transportMotive Γ A (Contextual.subTy C (Contextual.weaken Γ A)) x) (ordinaryApLeft Γ A x t)
  (Contextual.subTm t (Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x)))
abbrev ordinaryApBranch (Γ A C x t : Expression V) := Contextual.reflexivity C (ordinaryApply Γ A x t)
abbrev ordinaryAp (Γ A C x y p t : Expression V) :=
 Contextual.subTm (Contextual.basedJ A x (ordinaryApMotive Γ A C x t) (ordinaryApBranch Γ A C x t)) (Contextual.endpoint Γ A x y p)
variable (hC : Ty (Ω := Ω) Γ C)
 (ht : Tm (Ω := Ω) (Contextual.extend Γ A) (Contextual.subTy C (Contextual.weaken Γ A)) t) (hx : Tm (Ω := Ω) Γ A x)
def Tm.ordinaryApply : Tm (Ω := Ω) Γ C (Contextual.ordinaryApply Γ A x t) :=
 (ht.substitute hx.section).convert (hC.weakenSection hx)
def Tm.ordinaryApLeft : Tm (Ω := Ω) (Contextual.path A x)
 (Contextual.transportMotive Γ A (Contextual.subTy C (Contextual.weaken Γ A)) x) (Contextual.ordinaryApLeft Γ A x t) :=
 ((Tm.ordinaryApply hC ht hx).substitute hx.family.weaken).substitute hx.pathProjection
def Tm.ordinaryApMotive : Ty (Ω := Ω) (Contextual.path A x) (Contextual.ordinaryApMotive Γ A C x t) :=
 (Tm.ordinaryApLeft hC ht hx).identity (ht.substitute hx.pathProjection)
def Tm.ordinaryApLeftRoot : Equal (Ω := Ω)
 (Contextual.subTm (Contextual.ordinaryApLeft Γ A x t) (Contextual.root A x)) (Contextual.ordinaryApply Γ A x t) :=
 ((((Tm.ordinaryApply hC ht hx).substitute hx.family.weaken).subComp hx.pathProjection hx.root).transitive
  (Equal.subTm (.reflexive _) hx.rootProjection)).transitive ((Tm.ordinaryApply hC ht hx).weakenSection hx)
def Tm.ordinaryApMotiveRoot : Equal (Ω := Ω)
 (Contextual.subTy (Contextual.ordinaryApMotive Γ A C x t) (Contextual.root A x))
 (Contextual.identity C (Contextual.ordinaryApply Γ A x t) (Contextual.ordinaryApply Γ A x t)) :=
 ((Tm.ordinaryApLeft hC ht hx).identitySub (ht.substitute hx.pathProjection) hx.root).transitive
 (Equal.identity ((ht.family.transportRoot hx).transitive (hC.weakenSection hx))
  (Tm.ordinaryApLeftRoot hC ht hx)
  ((ht.subComp hx.pathProjection hx.root).transitive (Equal.subTm (.reflexive _) hx.rootProjection)))
def Tm.ordinaryApBranch : Tm (Ω := Ω) Γ (Contextual.subTy (Contextual.ordinaryApMotive Γ A C x t) (Contextual.root A x))
 (Contextual.ordinaryApBranch Γ A C x t) :=
 (Tm.ordinaryApply hC ht hx).reflexivity.convert (Tm.ordinaryApMotiveRoot hC ht hx).symmetric
variable (hy : Tm (Ω := Ω) Γ A y) (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p)
def Tm.ordinaryApMotiveEndpoint : Equal (Ω := Ω)
 (Contextual.subTy (Contextual.ordinaryApMotive Γ A C x t) (Contextual.endpoint Γ A x y p))
 (Contextual.identity C (Contextual.ordinaryApply Γ A x t) (Contextual.ordinaryApply Γ A y t)) := by
 apply ((Tm.ordinaryApLeft hC ht hx).identitySub (ht.substitute hx.pathProjection) (hx.endpoint hy hp)).transitive
 apply Equal.identity ((ht.family.transportEndpoint hx hy hp).transitive (hC.weakenSection hy))
 · exact ((((Tm.ordinaryApply hC ht hx).substitute hx.family.weaken).subComp hx.pathProjection (hx.endpoint hy hp)).transitive
     (Equal.subTm (.reflexive _) (hx.endpointProjection hy hp))).transitive
     ((Tm.ordinaryApply hC ht hx).weakenSection hy)
 · exact (ht.subComp hx.pathProjection (hx.endpoint hy hp)).transitive
     (Equal.subTm (.reflexive _) (hx.endpointProjection hy hp))

def Tm.ordinaryAp : Tm (Ω := Ω) Γ
 (Contextual.identity C (Contextual.ordinaryApply Γ A x t) (Contextual.ordinaryApply Γ A y t))
 (Contextual.ordinaryAp Γ A C x y p t) :=
 ((hx.basedJ (Tm.ordinaryApMotive hC ht hx) (Tm.ordinaryApBranch hC ht hx)).substitute (hx.endpoint hy hp)).convert
 (Tm.ordinaryApMotiveEndpoint hC ht hx hy hp)
end SquareKit.Internal.DependentJudgments.Contextual
