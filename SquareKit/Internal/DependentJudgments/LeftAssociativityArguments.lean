import SquareKit.Internal.DependentJudgments.LeftAssociativityFrame
import SquareKit.Internal.DependentJudgments.SourcePathArguments

/-! Generated dependent argument environment for arbitrary p,q,r. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory LeftConcatFrame LeftAssociativityFrame
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)} {Γ : Expression V}
namespace LeftAssociativityArguments
variable (C : ThreePaths Ω Γ)
abbrev atQ := LeftConcatArguments.atQ Γ C.first.A C.first.x C.first.y C.z C.first.p C.q
def atQTyped := LeftConcatArguments.atQTyped C.first.first C.first.second C.third C.first.proof C.middle
def wArgument := C.fourth.convert
  (LeftConcatArguments.finalTypeAt C.first.first C.first.second C.third C.first.proof C.middle).symmetric
abbrev atW := Contextual.pair (finalType Γ C.first.A C.first.x) (atQ C) C.w
def atWTyped := Sub.pair (finalFixedTyped C.first.first).family (atQTyped C) (wArgument C)
def wTypeAt : Equal (Ω := Ω)
    (subTy (wType Γ C.first.A C.first.x) (atW C)) C.first.A :=
  ((finalFixedTyped C.first.first).family.weakenPairType (finalFixedTyped C.first.first).family
    (atQTyped C) (wArgument C)).transitive
    (LeftConcatArguments.finalTypeAt C.first.first C.first.second C.third C.first.proof C.middle)
def zWAt : Equal (Ω := Ω) (subTm (zW Γ C.first.A C.first.x) (atW C)) C.z :=
  ((finalZTyped C.first.first).weakenPair (finalFixedTyped C.first.first).family
    (atQTyped C) (wArgument C)).transitive
    (LeftConcatArguments.finalZAt C.first.first C.first.second C.third C.first.proof C.middle)
def wAt : Equal (Ω := Ω) (subTm (w Γ C.first.A C.first.x) (atW C)) C.w :=
  (finalFixedTyped C.first.first).family.variablePair (atQTyped C) (wArgument C)
def rTypeAt : Equal (Ω := Ω) (subTy (rType Γ C.first.A C.first.x) (atW C))
    (Contextual.identity C.first.A C.z C.w) :=
  ((zWTyped C.first.first).identitySub (wTyped C.first.first) (atWTyped C)).transitive
    (Equal.identity (wTypeAt C) (zWAt C) (wAt C))
def rArgument := C.last.convert (rTypeAt C).symmetric
abbrev atR := Contextual.pair (rType Γ C.first.A C.first.x) (atW C) C.r
def atRTyped := Sub.pair (rTypeTyped C.first.first) (atWTyped C) (rArgument C)
def pathAtQ := ((PathArguments.generic C.first).under (pathTypeTyped C.first.first)
  (LeftConcatArguments.zArgument C.first.first C.first.second C.third C.first.proof)).under
  (qTypeTyped C.first.first) (LeftConcatArguments.qArgument C.first.first C.first.second C.third C.first.proof C.middle)
def pathAtW := (pathAtQ C).under (finalFixedTyped C.first.first).family (wArgument C)
def pathAtR := (pathAtW C).under (rTypeTyped C.first.first) (rArgument C)
def zAt : Equal (Ω := Ω) (subTm (inputs C.first.first).z (atR C)) C.z :=
  ((zWTyped C.first.first).weakenPair (rTypeTyped C.first.first) (atWTyped C) (rArgument C)).transitive (zWAt C)
def fourthAt : Equal (Ω := Ω) (subTm (inputs C.first.first).w (atR C)) C.w :=
  ((wTyped C.first.first).weakenPair (rTypeTyped C.first.first) (atWTyped C) (rArgument C)).transitive (wAt C)
def qAtQ : Equal (Ω := Ω) (subTm (LeftConcatFrame.q Γ C.first.A C.first.x) (atQ C)) C.q :=
  (qTypeTyped C.first.first).variablePair
    (LeftConcatArguments.atZTyped C.first.first C.first.second C.third C.first.proof)
    (LeftConcatArguments.qArgument C.first.first C.first.second C.third C.first.proof C.middle)
def qAtW : Equal (Ω := Ω)
    (subTm (subTm (LeftConcatFrame.q Γ C.first.A C.first.x) (wProjection Γ C.first.A C.first.x)) (atW C)) C.q :=
  ((qTyped C.first.first).weakenPair (finalFixedTyped C.first.first).family (atQTyped C) (wArgument C)).transitive (qAtQ C)
def qAt : Equal (Ω := Ω) (subTm (inputs C.first.first).q (atR C)) C.q :=
  ((qWTyped C.first.first).weakenPair (rTypeTyped C.first.first) (atWTyped C) (rArgument C)).transitive (qAtW C)
def rAt : Equal (Ω := Ω) (subTm (inputs C.first.first).r (atR C)) C.r :=
  (rTypeTyped C.first.first).variablePair (atWTyped C) (rArgument C)
def motiveAt : Equal (Ω := Ω) (subTy (inputs C.first.first).motive (atR C)) C.motive :=
  ((inputs C.first.first).motiveSub (atRTyped C)).transitive
    (((inputs C.first.first).substitute (atRTyped C)).motiveCongr
      (pathAtR C).carrier (pathAtR C).first (pathAtR C).second (zAt C) (fourthAt C)
      (pathAtR C).proof (qAt C) (rAt C))

end LeftAssociativityArguments
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
