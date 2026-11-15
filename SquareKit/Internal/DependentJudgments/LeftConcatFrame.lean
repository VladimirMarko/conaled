import SquareKit.Internal.DependentJudgments.PresentedSquares

/-! The left-path concatenation motive retains z and q : y = z as an
explicit dependent tail. All displayed values are generated source terms. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ A x : Expression V}

namespace LeftConcatFrame
abbrev pathProjection (Γ A x : Expression V) :=
  Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x)
abbrev pathType (Γ A x : Expression V) := subTy (subTy A (Contextual.weaken Γ A)) (pathProjection Γ A x)
abbrev fixed (Γ A x : Expression V) := subTm (subTm x (Contextual.weaken Γ A)) (pathProjection Γ A x)
abbrev moving (Γ A x : Expression V) := subTm (Contextual.generic Γ A) (pathProjection Γ A x)
abbrev withZ (Γ A x : Expression V) := Contextual.extend (path A x) (pathType Γ A x)
abbrev zProjection (Γ A x : Expression V) := Contextual.weaken (path A x) (pathType Γ A x)
abbrev zType (Γ A x : Expression V) := subTy (pathType Γ A x) (zProjection Γ A x)
abbrev z (Γ A x : Expression V) := Contextual.generic (path A x) (pathType Γ A x)
abbrev fixedZ (Γ A x : Expression V) := subTm (fixed Γ A x) (zProjection Γ A x)
abbrev movingZ (Γ A x : Expression V) := subTm (moving Γ A x) (zProjection Γ A x)
abbrev qType (Γ A x : Expression V) := Contextual.identity (zType Γ A x) (movingZ Γ A x) (z Γ A x)
abbrev withQ (Γ A x : Expression V) := Contextual.extend (withZ Γ A x) (qType Γ A x)
abbrev qProjection (Γ A x : Expression V) := Contextual.weaken (withZ Γ A x) (qType Γ A x)
abbrev finalType (Γ A x : Expression V) := subTy (zType Γ A x) (qProjection Γ A x)
abbrev finalFixed (Γ A x : Expression V) := subTm (fixedZ Γ A x) (qProjection Γ A x)
abbrev finalMoving (Γ A x : Expression V) := subTm (movingZ Γ A x) (qProjection Γ A x)
abbrev finalZ (Γ A x : Expression V) := subTm (z Γ A x) (qProjection Γ A x)
abbrev q (Γ A x : Expression V) := Contextual.generic (withZ Γ A x) (qType Γ A x)
abbrev motive (Γ A x : Expression V) := Contextual.identity (finalType Γ A x) (finalFixed Γ A x) (finalZ Γ A x)
abbrev tail (Γ A x : Expression V) : Reference.Tail V := .cons (pathType Γ A x) (.cons (qType Γ A x) .nil)

variable (hx : Tm (Ω := Ω) Γ A x)
def pathTypeTyped : Ty (Ω := Ω) (path A x) (pathType Γ A x) :=
  (hx.family.substitute hx.family.weaken).substitute hx.pathProjection
def fixedTyped : Tm (Ω := Ω) (path A x) (pathType Γ A x) (fixed Γ A x) :=
  (hx.substitute hx.family.weaken).substitute hx.pathProjection
def movingTyped : Tm (Ω := Ω) (path A x) (pathType Γ A x) (moving Γ A x) :=
  hx.family.generic.substitute hx.pathProjection
def zTyped : Tm (Ω := Ω) (withZ Γ A x) (zType Γ A x) (z Γ A x) :=
  (pathTypeTyped hx).generic
def fixedZTyped : Tm (Ω := Ω) (withZ Γ A x) (zType Γ A x) (fixedZ Γ A x) :=
  (fixedTyped hx).substitute (pathTypeTyped hx).weaken
def movingZTyped : Tm (Ω := Ω) (withZ Γ A x) (zType Γ A x) (movingZ Γ A x) :=
  (movingTyped hx).substitute (pathTypeTyped hx).weaken
def qTypeTyped : Ty (Ω := Ω) (withZ Γ A x) (qType Γ A x) :=
  (movingZTyped hx).identity (zTyped hx)
def finalFixedTyped : Tm (Ω := Ω) (withQ Γ A x) (finalType Γ A x) (finalFixed Γ A x) :=
  (fixedZTyped hx).substitute (qTypeTyped hx).weaken
def finalMovingTyped : Tm (Ω := Ω) (withQ Γ A x) (finalType Γ A x) (finalMoving Γ A x) :=
  (movingZTyped hx).substitute (qTypeTyped hx).weaken
def finalZTyped : Tm (Ω := Ω) (withQ Γ A x) (finalType Γ A x) (finalZ Γ A x) :=
  (zTyped hx).substitute (qTypeTyped hx).weaken
def qTyped : Tm (Ω := Ω) (withQ Γ A x)
    (Contextual.identity (finalType Γ A x) (finalMoving Γ A x) (finalZ Γ A x)) (q Γ A x) :=
  (qTypeTyped hx).generic.convert ((movingZTyped hx).identitySub (zTyped hx) (qTypeTyped hx).weaken)
def motiveTyped : Ty (Ω := Ω) (withQ Γ A x) (motive Γ A x) :=
  (finalFixedTyped hx).identity (finalZTyped hx)
def tailTyped : Reference.Presented Ω (path A x) (tail Γ A x) :=
  .cons (pathTypeTyped hx) (.cons (qTypeTyped hx) (.nil (qTypeTyped hx).extend))

/-- The generic moving point becomes the fixed point at the reflexive root. -/
def movingRoot : Equal (Ω := Ω) (subTm (moving Γ A x) (root A x)) x :=
  (hx.family.generic.subComp hx.pathProjection hx.root).transitive
    ((Equal.subTm (.reflexive _) hx.rootProjection).transitive hx.sectionGeneric)
def fixedRoot : Equal (Ω := Ω) (subTm (fixed Γ A x) (root A x)) x :=
  ((hx.substitute hx.family.weaken).subComp hx.pathProjection hx.root).transitive
    ((Equal.subTm (.reflexive _) hx.rootProjection).transitive (hx.weakenSection hx))

/-- The first root lift retains z, the second retains q with its dependent type. -/
def rootLiftZ := hx.root.lift (pathTypeTyped hx)
def rootLiftQ := (rootLiftZ hx).lift (qTypeTyped hx)

def endpointsRoot : Equal (Ω := Ω)
    (subTm (finalMoving Γ A x) ((tail Γ A x).map Γ (root A x)))
    (subTm (finalFixed Γ A x) ((tail Γ A x).map Γ (root A x))) :=
  (movingZTyped hx).weakenLiftEqual (fixedZTyped hx) (qTypeTyped hx) (rootLiftZ hx)
    ((movingTyped hx).weakenLiftEqual (fixedTyped hx) (pathTypeTyped hx) hx.root
      ((movingRoot hx).transitive (fixedRoot hx).symmetric))

/-- The selected branch is the retained q, pulled back through the actual
root-tail map. Its family conversion changes the moving endpoint to x. -/
def branch : Tm (Ω := Ω) ((tail Γ A x).rootDomain Γ A x)
    (subTy (motive Γ A x) ((tail Γ A x).map Γ (root A x)))
    (subTm (q Γ A x) ((tail Γ A x).map Γ (root A x))) :=
  ((qTyped hx).substitute (rootLiftQ hx)).convert
    (((finalMovingTyped hx).identitySub (finalZTyped hx) (rootLiftQ hx)).transitive
      ((Equal.identity (.reflexive _) (endpointsRoot hx) (.reflexive _)).transitive
        ((finalFixedTyped hx).identitySub (finalZTyped hx) (rootLiftQ hx)).symmetric))

/-- The first-path eliminator with its nonempty dependent tail is constructed
from generated J. The supplied source argument contains no semantic codes. -/
def genericConcat := Presented.eliminate hx (tailTyped hx) (motiveTyped hx) (branch hx)
def genericBeta := Presented.beta hx (tailTyped hx) (motiveTyped hx) (branch hx)
end LeftConcatFrame
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
