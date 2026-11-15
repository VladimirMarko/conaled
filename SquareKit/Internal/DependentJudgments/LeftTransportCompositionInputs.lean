import SquareKit.Internal.DependentJudgments.SourcePath
import SquareKit.Internal.DependentJudgments.LeftConcatRecipe
import SquareKit.Internal.DependentJudgments.LeftConcatenationSubstitution
import SquareKit.Internal.DependentJudgments.TelescopeTransport

/-! Transport composition with an arbitrary dependent family. The substitution
and reflexive branch equations below are generated source derivations. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)} {Γ Δ : Expression V}
namespace LeftTransportComposition
private theorem transport_subst {W : Type} (s : V → Expression W)
    (g a b x y p u : Expression V) :
    (Contextual.transport g a b x y p u).subst s =
      Contextual.transport (g.subst s) (a.subst s) (b.subst s) (x.subst s)
        (y.subst s) (p.subst s) (u.subst s) := by
  simp only [Contextual.transport, Contextual.basedJ, Contextual.transportMotive,
    Contextual.endpoint, Contextual.pathFamily, Contextual.sectionSub,
    LeftConcatRecipe.subTm_subst, LeftConcatRecipe.subTy_subst,
    LeftConcatRecipe.path_subst, LeftConcatRecipe.telNil_subst,
    LeftConcatRecipe.pair_subst, LeftConcatRecipe.extend_subst,
    LeftConcatRecipe.weaken_subst, LeftConcatRecipe.generic_subst,
    LeftConcatRecipe.identity_subst, LeftConcatRecipe.identitySub_subst,
    LeftConcatRecipe.j_subst]

def congr {g g' a a' b b' x x' y y' p p' u u' : Expression V}
    (hg : Equal (Ω := Ω) g g') (ha : Equal (Ω := Ω) a a')
    (hb : Equal (Ω := Ω) b b') (hx : Equal (Ω := Ω) x x')
    (hy : Equal (Ω := Ω) y y') (hp : Equal (Ω := Ω) p p')
    (hu : Equal (Ω := Ω) u u') :
    Equal (Ω := Ω) (Contextual.transport g a b x y p u)
      (Contextual.transport g' a' b' x' y' p' u') := by
  have e := Equal.recipe (Contextual.transport (.var 0) (.var 1) (.var 2)
    (.var 3) (.var 4) (.var 5) (.var 6) : Expression (Fin 7))
    ![g,a,b,x,y,p,u] ![g',a',b',x',y',p',u']
    (Fin.cases hg (Fin.cases ha (Fin.cases hb (Fin.cases hx (Fin.cases hy
      (Fin.cases hp (Fin.cases hu (fun i => nomatch i))))))))
  rw [transport_subst, transport_subst] at e
  simpa [Term.subst, Term.var, FinitaryTerm.bind] using e

structure Inputs (Ω : List (Judgment V)) (Γ : Expression V) where
  first : SourcePath Ω Γ
  B : Expression V
  z : Expression V
  q : Expression V
  u : Expression V
  family : Ty (Ω := Ω) (Contextual.extend Γ first.A) B
  third : Tm (Ω := Ω) Γ first.A z
  secondPath : Tm (Ω := Ω) Γ (Contextual.identity first.A first.y z) q
  element : Tm (Ω := Ω) Γ (subTy B (sectionSub Γ first.A first.x)) u
namespace Inputs
variable (C : Inputs Ω Γ)
abbrev composite := leftConcat Γ C.first.A C.first.x C.first.y C.z C.first.p C.q
abbrev left := Contextual.transport Γ C.first.A C.B C.first.x C.z C.composite C.u
abbrev intermediate := Contextual.transport Γ C.first.A C.B C.first.x C.first.y C.first.p C.u
abbrev right := Contextual.transport Γ C.first.A C.B C.first.y C.z C.q C.intermediate
abbrev resultType := subTy C.B (sectionSub Γ C.first.A C.z)
def compositeTyped := C.first.first.leftConcat C.first.second C.third C.first.proof C.secondPath
def intermediateTyped := Tm.transport C.family C.first.first C.first.second C.first.proof C.element
def leftTyped := Tm.transport C.family C.first.first C.third C.compositeTyped C.element
def rightTyped := Tm.transport C.family C.first.second C.third C.secondPath C.intermediateTyped
abbrev motive := Contextual.identity C.resultType C.left C.right
def motiveTyped : Ty (Ω := Ω) Γ C.motive := C.leftTyped.identity C.rightTyped

def substitute {σ : Expression V} (hs : Sub (Ω := Ω) Δ Γ σ) : Inputs Ω Δ where
  first := C.first.substitute hs
  B := subTy C.B (liftSyntax Δ C.first.A σ)
  z := subTm C.z σ
  q := subTm C.q σ
  u := subTm C.u σ
  family := C.family.substitute (hs.lift C.first.first.family)
  third := C.third.substitute hs
  secondPath := (C.secondPath.substitute hs).convert (C.first.second.identitySub C.third hs)
  element := (C.element.substitute hs).convert (C.family.sectionLift hs C.first.first).symmetric

def leftSub {σ : Expression V} (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm C.left σ) (C.substitute hs).left :=
  (Tm.transportSub C.family C.first.first C.third C.compositeTyped C.element hs).transitive
    (congr (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _)
      (C.first.first.leftConcatSub C.first.second C.third C.first.proof C.secondPath hs) (.reflexive _))
def rightSub {σ : Expression V} (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm C.right σ) (C.substitute hs).right :=
  (Tm.transportSub C.family C.first.second C.third C.secondPath C.intermediateTyped hs).transitive
    (congr (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _)
      (Tm.transportSub C.family C.first.first C.first.second C.first.proof C.element hs))
def motiveSub {σ : Expression V} (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTy C.motive σ) (C.substitute hs).motive :=
  (C.leftTyped.identitySub C.rightTyped hs).transitive
    (Equal.identity (C.family.sectionLift hs C.third).symmetric (C.leftSub hs) (C.rightSub hs))

def reflexiveCase (ey : Equal (Ω := Ω) C.first.y C.first.x)
    (ep : Equal (Ω := Ω) C.first.p (Contextual.reflexivity C.first.A C.first.x)) :
    Equal (Ω := Ω) C.left C.right := by
  have hq := C.secondPath.convert (Equal.identity (.reflexive _) ey (.reflexive _))
  have inner := (Equal.leftConcat (.reflexive _) (.reflexive _) (.reflexive _) ey
    (.reflexive _) ep (.reflexive _)).transitive (C.first.first.leftConcatReflLeft C.third hq)
  have eleft : Equal (Ω := Ω) C.left (Contextual.transport Γ C.first.A C.B C.first.x C.z C.q C.u) := congr (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _)
    (.reflexive _) inner (show Equal (Ω := Ω) C.u C.u from .reflexive _)
  have emid : Equal (Ω := Ω) C.intermediate C.u := (congr (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _)
    ey ep (show Equal (Ω := Ω) C.u C.u from .reflexive _)).transitive
      (Tm.transportRefl C.family C.first.first C.element)
  exact eleft.transitive (congr (.reflexive _) (.reflexive _) (.reflexive _) ey
    (.reflexive _) (.reflexive _) emid).symmetric

def rootBranch {σ : Expression V} (hs : Sub (Ω := Ω) Δ Γ σ) (R : ReflexiveRoot C.first hs) :
    Tm (Ω := Ω) Δ (subTy C.motive σ)
      (Contextual.reflexivity (C.substitute hs).resultType (C.substitute hs).left) :=
  ((C.substitute hs).leftTyped.reflexivity.convert
    (Equal.identity (.reflexive _) (.reflexive _)
      ((C.substitute hs).reflexiveCase R.endpoint R.path))).convert (C.motiveSub hs).symmetric
def motiveCongr {D : Inputs Ω Γ}
    (hA : Equal (Ω := Ω) C.first.A D.first.A) (hB : Equal (Ω := Ω) C.B D.B)
    (hx : Equal (Ω := Ω) C.first.x D.first.x) (hy : Equal (Ω := Ω) C.first.y D.first.y)
    (hz : Equal (Ω := Ω) C.z D.z) (hp : Equal (Ω := Ω) C.first.p D.first.p)
    (hq : Equal (Ω := Ω) C.q D.q) (hu : Equal (Ω := Ω) C.u D.u) :
    Equal (Ω := Ω) C.motive D.motive :=
  Equal.identity (Equal.subTy hB (Equal.pair hA (.reflexive _) hz))
    (congr (.reflexive _) hA hB hx hz (Equal.leftConcat (.reflexive _) hA hx hy hz hp hq) hu)
    (congr (.reflexive _) hA hB hy hz hq (congr (.reflexive _) hA hB hx hy hp hu))
end Inputs
end LeftTransportComposition
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
