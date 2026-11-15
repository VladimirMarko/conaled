import SquareKit.Internal.DependentJudgments.LeftConcatenationSubstitution

/-! Generic path data, including its reflexive-root equation, through any
explicitly presented finite dependent tail. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory LeftConcatFrame
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)} {Γ A x : Expression V}
namespace PresentedPath
abbrev pathProof (Γ A x : Expression V) := Contextual.generic (Contextual.extend Γ A) (Contextual.pathFamily Γ A x)
variable (hx : Tm (Ω := Ω) Γ A x)
def pathProofTyped : Tm (Ω := Ω) (path A x) (Contextual.identity (pathType Γ A x) (fixed Γ A x) (moving Γ A x))
    (pathProof Γ A x) :=
  ((hx.pathFamily.generic).recontext hx.pathDef.symmetric).convert
    ((hx.substitute hx.family.weaken).identitySub hx.family.generic hx.pathProjection)
def pathProofRoot : Equal (Ω := Ω) (subTm (pathProof Γ A x) (root A x)) (Contextual.reflexivity A x) :=
  (Equal.subTm (.reflexive _) hx.rootDef).transitive
    (hx.pathFamily.variablePair hx.section (hx.reflexivity.convert (hx.pathFamilySection hx).symmetric))
def pathTypeRoot : Equal (Ω := Ω) (subTy (pathType Γ A x) (root A x)) A :=
  ((hx.family.substitute hx.family.weaken).subComp hx.pathProjection hx.root).transitive
    ((Equal.subTy (.reflexive _) hx.rootProjection).transitive (hx.family.weakenSection hx))

variable {T : Reference.Tail V} (hT : Reference.Presented Ω (path A x) T)
abbrev carrier := subTy (pathType Γ A x) (T.projection (path A x))
abbrev first := subTm (fixed Γ A x) (T.projection (path A x))
abbrev second := subTm (moving Γ A x) (T.projection (path A x))
abbrev proof := subTm (pathProof Γ A x) (T.projection (path A x))
def firstTyped : Tm (Ω := Ω) (T.total (path A x)) (carrier (Γ := Γ) (A := A) (x := x) (T := T))
    (first (Γ := Γ) (A := A) (x := x) (T := T)) :=
  (fixedTyped hx).substitute (Presented.projection hT)
def secondTyped : Tm (Ω := Ω) (T.total (path A x)) (carrier (Γ := Γ) (A := A) (x := x) (T := T))
    (second (Γ := Γ) (A := A) (x := x) (T := T)) :=
  (movingTyped hx).substitute (Presented.projection hT)
def proofTyped : Tm (Ω := Ω) (T.total (path A x))
    (Contextual.identity (carrier (Γ := Γ) (A := A) (x := x) (T := T))
      (first (Γ := Γ) (A := A) (x := x) (T := T)) (second (Γ := Γ) (A := A) (x := x) (T := T)))
    (proof (Γ := Γ) (A := A) (x := x) (T := T)) :=
  ((pathProofTyped hx).substitute (Presented.projection hT)).convert
    ((fixedTyped hx).identitySub (movingTyped hx) (Presented.projection hT))
def firstRoot : Equal (Ω := Ω)
    (subTm (first (Γ := Γ) (A := A) (x := x) (T := T)) (T.map Γ (root A x)))
    (subTm x ((T.reindex Γ (root A x)).projection Γ)) :=
  (Presented.termSquare hT (fixedTyped hx) hx.family.context hx.root).transitive
    (Equal.subTm (fixedRoot hx) (.reflexive _))
def secondRoot : Equal (Ω := Ω)
    (subTm (second (Γ := Γ) (A := A) (x := x) (T := T)) (T.map Γ (root A x)))
    (subTm (first (Γ := Γ) (A := A) (x := x) (T := T)) (T.map Γ (root A x))) :=
  ((Presented.termSquare hT (movingTyped hx) hx.family.context hx.root).transitive
    (Equal.subTm (movingRoot hx) (.reflexive _))).transitive (firstRoot hx hT).symmetric
def carrierRoot : Equal (Ω := Ω)
    (subTy (carrier (Γ := Γ) (A := A) (x := x) (T := T)) (T.map Γ (root A x)))
    (subTy A ((T.reindex Γ (root A x)).projection Γ)) :=
  (Presented.typeSquare hT (pathTypeTyped hx) hx.family.context hx.root).transitive
    (Equal.subTy (pathTypeRoot hx) (.reflexive _))
def proofRoot : Equal (Ω := Ω)
    (subTm (proof (Γ := Γ) (A := A) (x := x) (T := T)) (T.map Γ (root A x)))
    (Contextual.reflexivity
      (subTy (carrier (Γ := Γ) (A := A) (x := x) (T := T)) (T.map Γ (root A x)))
      (subTm (first (Γ := Γ) (A := A) (x := x) (T := T)) (T.map Γ (root A x)))) :=
  (Presented.termSquare hT (pathProofTyped hx) hx.family.context hx.root).transitive
    ((Equal.subTm (pathProofRoot hx) (.reflexive _)).transitive
      ((hx.reflSub (Presented.projection (hT.reindex hx.family.context hx.root))).transitive
        (Equal.reflexivity (carrierRoot hx hT).symmetric (firstRoot hx hT).symmetric)))
end PresentedPath
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
