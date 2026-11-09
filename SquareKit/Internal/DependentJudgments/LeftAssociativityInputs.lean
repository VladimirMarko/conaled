import SquareKit.Internal.DependentJudgments.SourcePath
import SquareKit.Internal.DependentJudgments.LeftConcatRecipe

/-! The mathematical associativity statement and its source-substitution law.
The inputs are typed paths; model-indexed codes are absent. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)} {Γ Δ : Expression V}
structure ThreePaths (Ω : List (Judgment V)) (Γ : Expression V) where
  first : SourcePath Ω Γ
  z : Expression V
  w : Expression V
  q : Expression V
  r : Expression V
  third : Tm (Ω := Ω) Γ first.A z
  fourth : Tm (Ω := Ω) Γ first.A w
  middle : Tm (Ω := Ω) Γ (Contextual.identity first.A first.y z) q
  last : Tm (Ω := Ω) Γ (Contextual.identity first.A z w) r
namespace ThreePaths
variable (C : ThreePaths Ω Γ)
abbrev left := leftConcat Γ C.first.A C.first.x C.z C.w
  (leftConcat Γ C.first.A C.first.x C.first.y C.z C.first.p C.q) C.r
abbrev right := leftConcat Γ C.first.A C.first.x C.first.y C.w C.first.p
  (leftConcat Γ C.first.A C.first.y C.z C.w C.q C.r)
def middleComposite := C.first.first.leftConcat C.first.second C.third C.first.proof C.middle
def lastComposite := C.first.second.leftConcat C.third C.fourth C.middle C.last
def leftTyped := C.first.first.leftConcat C.third C.fourth C.middleComposite C.last
def rightTyped := C.first.first.leftConcat C.first.second C.fourth C.first.proof C.lastComposite
abbrev motive := Contextual.identity (Contextual.identity C.first.A C.first.x C.w) C.left C.right
def motiveTyped : Ty (Ω := Ω) Γ C.motive := C.leftTyped.identity C.rightTyped
def substitute {σ : Expression V} (hs : Sub (Ω := Ω) Δ Γ σ) : ThreePaths Ω Δ where
  first := C.first.substitute hs
  z := subTm C.z σ
  w := subTm C.w σ
  q := subTm C.q σ
  r := subTm C.r σ
  third := C.third.substitute hs
  fourth := C.fourth.substitute hs
  middle := (C.middle.substitute hs).convert (C.first.second.identitySub C.third hs)
  last := (C.last.substitute hs).convert (C.third.identitySub C.fourth hs)
def leftSub {σ : Expression V} (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm C.left σ) (C.substitute hs).left :=
  (C.first.first.leftConcatSub C.third C.fourth C.middleComposite C.last hs).transitive
    (Equal.leftConcat (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _)
      (C.first.first.leftConcatSub C.first.second C.third C.first.proof C.middle hs) (.reflexive _))
def rightSub {σ : Expression V} (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm C.right σ) (C.substitute hs).right :=
  (C.first.first.leftConcatSub C.first.second C.fourth C.first.proof C.lastComposite hs).transitive
    (Equal.leftConcat (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _)
      (C.first.second.leftConcatSub C.third C.fourth C.middle C.last hs))
def motiveSub {σ : Expression V} (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTy C.motive σ) (C.substitute hs).motive :=
  (C.leftTyped.identitySub C.rightTyped hs).transitive
    (Equal.identity (C.first.first.identitySub C.fourth hs) (C.leftSub hs) (C.rightSub hs))
def reflexiveCase (ey : Equal (Ω := Ω) C.first.y C.first.x)
    (ep : Equal (Ω := Ω) C.first.p (Contextual.reflexivity C.first.A C.first.x)) :
    Equal (Ω := Ω) C.left C.right := by
  have hq := C.middle.convert (Equal.identity (.reflexive _) ey (.reflexive _))
  have inner := (Equal.leftConcat (.reflexive _) (.reflexive _) (.reflexive _) ey (.reflexive _) ep (.reflexive _)).transitive
    (C.first.first.leftConcatReflLeft C.third hq)
  have leftEq : Equal (Ω := Ω) C.left (leftConcat Γ C.first.A C.first.y C.z C.w C.q C.r) := (Equal.leftConcat (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) inner (.reflexive _)).transitive
    (Equal.leftConcat (.reflexive _) (.reflexive _) ey.symmetric (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _))
  have rightEq := (Equal.leftConcat (.reflexive _) (.reflexive _) (.reflexive _) ey (.reflexive _) ep (.reflexive _)).transitive
    (C.first.first.leftConcatReflLeft C.fourth
      (C.lastComposite.convert (Equal.identity (.reflexive _) ey (.reflexive _))))
  exact leftEq.transitive rightEq.symmetric
def rootBranch {σ : Expression V} (hs : Sub (Ω := Ω) Δ Γ σ) (R : ReflexiveRoot C.first hs) :
    Tm (Ω := Ω) Δ (subTy C.motive σ)
      (Contextual.reflexivity (Contextual.identity (subTy C.first.A σ) (subTm C.first.x σ) (subTm C.w σ))
        (C.substitute hs).left) :=
  ((C.substitute hs).leftTyped.reflexivity.convert
    (Equal.identity (.reflexive _) (.reflexive _) ((C.substitute hs).reflexiveCase R.endpoint R.path))).convert
      (C.motiveSub hs).symmetric
def motiveCongr {D : ThreePaths Ω Γ}
    (hA : Equal (Ω := Ω) C.first.A D.first.A) (hx : Equal (Ω := Ω) C.first.x D.first.x)
    (hy : Equal (Ω := Ω) C.first.y D.first.y) (hz : Equal (Ω := Ω) C.z D.z)
    (hw : Equal (Ω := Ω) C.w D.w) (hp : Equal (Ω := Ω) C.first.p D.first.p)
    (hq : Equal (Ω := Ω) C.q D.q) (hr : Equal (Ω := Ω) C.r D.r) : Equal (Ω := Ω) C.motive D.motive :=
  Equal.identity (Equal.identity hA hx hw)
    (Equal.leftConcat (.reflexive _) hA hx hz hw (Equal.leftConcat (.reflexive _) hA hx hy hz hp hq) hr)
    (Equal.leftConcat (.reflexive _) hA hx hy hw hp (Equal.leftConcat (.reflexive _) hA hy hz hw hq hr))

end ThreePaths
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
