import SquareKit.Internal.DependentJudgments.LeftConcatFrame

/-! Application of the retained left-path eliminator to typed arguments.
The builder constructs dependent argument environments and normalizes their
source result type without all-model annotations at the caller. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ A x y z p q : Expression V}

namespace LeftConcatArguments
open LeftConcatFrame
abbrev atPath (Γ A x y p : Expression V) := Contextual.endpoint Γ A x y p
abbrev atZ (Γ A x y z p : Expression V) := Contextual.pair (pathType Γ A x) (atPath Γ A x y p) z
abbrev atQ (Γ A x y z p q : Expression V) := Contextual.pair (qType Γ A x) (atZ Γ A x y z p) q
variable (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
  (hz : Tm (Ω := Ω) Γ A z) (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p)
  (hq : Tm (Ω := Ω) Γ (Contextual.identity A y z) q)

def pathTypeAt : Equal (Ω := Ω) (subTy (pathType Γ A x) (atPath Γ A x y p)) A :=
  ((hx.family.substitute hx.family.weaken).subComp hx.pathProjection (hx.endpoint hy hp)).transitive
    ((Equal.subTy (.reflexive _) (hx.endpointProjection hy hp)).transitive (hx.family.weakenSection hy))
def fixedAt : Equal (Ω := Ω) (subTm (fixed Γ A x) (atPath Γ A x y p)) x :=
  ((hx.substitute hx.family.weaken).subComp hx.pathProjection (hx.endpoint hy hp)).transitive
    ((Equal.subTm (.reflexive _) (hx.endpointProjection hy hp)).transitive (hx.weakenSection hy))
def movingAt : Equal (Ω := Ω) (subTm (moving Γ A x) (atPath Γ A x y p)) y :=
  (hx.family.generic.subComp hx.pathProjection (hx.endpoint hy hp)).transitive
    ((Equal.subTm (.reflexive _) (hx.endpointProjection hy hp)).transitive hy.sectionGeneric)
def zArgument := hz.convert (pathTypeAt hx hy hp).symmetric
def atZTyped : Sub (Ω := Ω) Γ (withZ Γ A x) (atZ Γ A x y z p) :=
  Sub.pair (pathTypeTyped hx) (hx.endpoint hy hp) (zArgument hx hy hz hp)
def zTypeAt : Equal (Ω := Ω) (subTy (zType Γ A x) (atZ Γ A x y z p)) A :=
  ((pathTypeTyped hx).weakenPairType (pathTypeTyped hx) (hx.endpoint hy hp) (zArgument hx hy hz hp)).transitive (pathTypeAt hx hy hp)
def fixedZAt : Equal (Ω := Ω) (subTm (fixedZ Γ A x) (atZ Γ A x y z p)) x :=
  ((fixedTyped hx).weakenPair (pathTypeTyped hx) (hx.endpoint hy hp) (zArgument hx hy hz hp)).transitive (fixedAt hx hy hp)
def movingZAt : Equal (Ω := Ω) (subTm (movingZ Γ A x) (atZ Γ A x y z p)) y :=
  ((movingTyped hx).weakenPair (pathTypeTyped hx) (hx.endpoint hy hp) (zArgument hx hy hz hp)).transitive (movingAt hx hy hp)
def zAt : Equal (Ω := Ω) (subTm (LeftConcatFrame.z Γ A x) (atZ Γ A x y z p)) z :=
  (pathTypeTyped hx).variablePair (hx.endpoint hy hp) (zArgument hx hy hz hp)
def qTypeAt : Equal (Ω := Ω) (subTy (qType Γ A x) (atZ Γ A x y z p)) (Contextual.identity A y z) :=
  ((movingZTyped hx).identitySub (zTyped hx) (atZTyped hx hy hz hp)).transitive
    (Equal.identity (zTypeAt hx hy hz hp) (movingZAt hx hy hz hp) (zAt hx hy hz hp))
def qArgument := hq.convert (qTypeAt hx hy hz hp).symmetric
def atQTyped : Sub (Ω := Ω) Γ (withQ Γ A x) (atQ Γ A x y z p q) :=
  Sub.pair (qTypeTyped hx) (atZTyped hx hy hz hp) (qArgument hx hy hz hp hq)
def finalTypeAt : Equal (Ω := Ω) (subTy (finalType Γ A x) (atQ Γ A x y z p q)) A :=
  (((zTyped hx).family).weakenPairType (qTypeTyped hx) (atZTyped hx hy hz hp) (qArgument hx hy hz hp hq)).transitive (zTypeAt hx hy hz hp)
def finalFixedAt : Equal (Ω := Ω) (subTm (finalFixed Γ A x) (atQ Γ A x y z p q)) x :=
  ((fixedZTyped hx).weakenPair (qTypeTyped hx) (atZTyped hx hy hz hp) (qArgument hx hy hz hp hq)).transitive (fixedZAt hx hy hz hp)
def finalZAt : Equal (Ω := Ω) (subTm (finalZ Γ A x) (atQ Γ A x y z p q)) z :=
  ((zTyped hx).weakenPair (qTypeTyped hx) (atZTyped hx hy hz hp) (qArgument hx hy hz hp hq)).transitive (zAt hx hy hz hp)
def motiveAt : Equal (Ω := Ω) (subTy (motive Γ A x) (atQ Γ A x y z p q)) (Contextual.identity A x z) :=
  ((finalFixedTyped hx).identitySub (finalZTyped hx) (atQTyped hx hy hz hp hq)).transitive
    (Equal.identity (finalTypeAt hx hy hz hp hq) (finalFixedAt hx hy hz hp hq) (finalZAt hx hy hz hp hq))
end LeftConcatArguments

abbrev leftConcat (Γ A x y z p q : Expression V) :=
  subTm (j A x ((LeftConcatFrame.tail Γ A x).code (path A x))
    (LeftConcatFrame.motive Γ A x)
    (subTm (LeftConcatFrame.q Γ A x) ((LeftConcatFrame.tail Γ A x).map Γ (root A x))))
    (LeftConcatArguments.atQ Γ A x y z p q)

/-- Both input paths remain arbitrary. The operation eliminates p, retains
z and q in a dependent tail, and selects q at the reflexive root. -/
def Tm.leftConcat (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hz : Tm (Ω := Ω) Γ A z) (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p)
    (hq : Tm (Ω := Ω) Γ (Contextual.identity A y z) q) :
    Tm (Ω := Ω) Γ (Contextual.identity A x z) (leftConcat Γ A x y z p q) :=
  ((LeftConcatFrame.genericConcat hx).substitute (LeftConcatArguments.atQTyped hx hy hz hp hq)).convert
    (LeftConcatArguments.motiveAt hx hy hz hp hq)
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
