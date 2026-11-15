import SquareKit.Internal.DependentJudgments.LeftAssociativityInputs

/-! The associativity motive retains all four dependent declarations z,q,w,r
following the generic first path. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory LeftConcatFrame
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)} {Γ A x : Expression V}
namespace LeftAssociativityFrame
abbrev withW (Γ A x : Expression V) := Contextual.extend (withQ Γ A x) (finalType Γ A x)
abbrev wProjection (Γ A x : Expression V) := Contextual.weaken (withQ Γ A x) (finalType Γ A x)
abbrev wType (Γ A x : Expression V) := subTy (finalType Γ A x) (wProjection Γ A x)
abbrev w (Γ A x : Expression V) := Contextual.generic (withQ Γ A x) (finalType Γ A x)
abbrev zW (Γ A x : Expression V) := subTm (finalZ Γ A x) (wProjection Γ A x)
abbrev rType (Γ A x : Expression V) := Contextual.identity (wType Γ A x) (zW Γ A x) (w Γ A x)
abbrev withR (Γ A x : Expression V) := Contextual.extend (withW Γ A x) (rType Γ A x)
abbrev rProjection (Γ A x : Expression V) := Contextual.weaken (withW Γ A x) (rType Γ A x)
abbrev tail (Γ A x : Expression V) : Reference.Tail V := .cons (pathType Γ A x)
  (.cons (qType Γ A x) (.cons (finalType Γ A x) (.cons (rType Γ A x) .nil)))
variable (hx : Tm (Ω := Ω) Γ A x)
def firstQ := ((SourcePath.generic hx).substitute (pathTypeTyped hx).weaken).substitute (qTypeTyped hx).weaken
def firstW := (firstQ hx).substitute (finalFixedTyped hx).family.weaken
def zWTyped := (finalZTyped hx).substitute (finalFixedTyped hx).family.weaken
def wTyped := (finalFixedTyped hx).family.generic
def rTypeTyped : Ty (Ω := Ω) (withW Γ A x) (rType Γ A x) := (zWTyped hx).identity (wTyped hx)
def firstR := (firstW hx).substitute (rTypeTyped hx).weaken
def zRTyped := (zWTyped hx).substitute (rTypeTyped hx).weaken
def wRTyped := (wTyped hx).substitute (rTypeTyped hx).weaken
def qWTyped := ((qTyped hx).substitute (finalFixedTyped hx).family.weaken).convert
  ((finalMovingTyped hx).identitySub (finalZTyped hx) (finalFixedTyped hx).family.weaken)
def qRTyped := ((qWTyped hx).substitute (rTypeTyped hx).weaken).convert
  ((firstW hx).second.identitySub (zWTyped hx) (rTypeTyped hx).weaken)
def rTyped := (rTypeTyped hx).generic.convert
  ((zWTyped hx).identitySub (wTyped hx) (rTypeTyped hx).weaken)
def inputs : ThreePaths Ω (withR Γ A x) where
  first := firstR hx
  z := subTm (zW Γ A x) (rProjection Γ A x)
  w := subTm (w Γ A x) (rProjection Γ A x)
  q := subTm (subTm (LeftConcatFrame.q Γ A x) (wProjection Γ A x)) (rProjection Γ A x)
  r := Contextual.generic (withW Γ A x) (rType Γ A x)
  third := zRTyped hx
  fourth := wRTyped hx
  middle := qRTyped hx
  last := rTyped hx

def tailTyped : Reference.Presented Ω (path A x) (tail Γ A x) :=
  .cons (pathTypeTyped hx) (.cons (qTypeTyped hx) (.cons (finalFixedTyped hx).family
    (.cons (rTypeTyped hx) (.nil (rTypeTyped hx).extend))))
def rootW := (rootLiftQ hx).lift (finalFixedTyped hx).family
def rootR := (rootW hx).lift (rTypeTyped hx)
def rootEvidence : ReflexiveRoot (inputs hx).first (rootR hx) :=
  ((((ReflexiveRoot.generic hx).under (pathTypeTyped hx)).under (qTypeTyped hx)).under
    (finalFixedTyped hx).family).under (rTypeTyped hx)
def branch := (inputs hx).rootBranch (rootR hx) (rootEvidence hx)
def derivation := Presented.eliminate hx (tailTyped hx) (inputs hx).motiveTyped (branch hx)
end LeftAssociativityFrame
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
