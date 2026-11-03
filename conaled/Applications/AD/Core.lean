import Squares
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Differentiation specified before its implementation

This is the first-order differentiable category of Elliott's *The simple
essence of automatic differentiation* (2018), with its invariant made a field.
The invariant is Mathlib's analytic `HasFDerivAt`, not a formal chain-rule
calculus.  Consequently a zero or otherwise invented tangent cannot certify
an arbitrary primal computation merely by making the primal square commute.

`DMap` works between real normed spaces.  Its cartesian operations are checked
using the actual chain and product rules.  `tangentSquare` is the object-level
commuting square; `tangent_correct` supplies the additional derivative claim.
There is deliberately no cartesian-closed instance on arbitrary normed spaces.
-/

noncomputable section

namespace Applications.AD

variable {E F G H : Type}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A primal computation and a genuine Fréchet derivative at every point. -/
structure DMap (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  primal : E → F
  derivative : E → E →L[ℝ] F
  correct : ∀ x, HasFDerivAt primal (derivative x) x

namespace DMap

@[ext] theorem ext {f g : DMap E F} (h : ∀ x, f.primal x = g.primal x) : f = g := by
  have hp : f.primal = g.primal := funext h
  have hd : f.derivative = g.derivative := by
    funext x
    exact (f.correct x).unique (hp.symm ▸ g.correct x)
  cases f
  cases g
  cases hp
  cases hd
  rfl

def ident : DMap E E where
  primal := id
  derivative _ := ContinuousLinearMap.id ℝ E
  correct := hasFDerivAt_id

def comp (g : DMap F G) (f : DMap E F) : DMap E G where
  primal x := g.primal (f.primal x)
  derivative x := (g.derivative (f.primal x)).comp (f.derivative x)
  correct x := (g.correct (f.primal x)).comp x (f.correct x)

def constant (y : F) : DMap E F where
  primal _ := y
  derivative _ := 0
  correct := hasFDerivAt_const y

/-- Every continuous linear map differentiates to itself. -/
def linear (L : E →L[ℝ] F) : DMap E F where
  primal := L
  derivative _ := L
  correct _ := L.hasFDerivAt

def fst : DMap (E × F) E := linear (ContinuousLinearMap.fst ℝ E F)
def snd : DMap (E × F) F := linear (ContinuousLinearMap.snd ℝ E F)

def pair (f : DMap E F) (g : DMap E G) : DMap E (F × G) where
  primal x := (f.primal x, g.primal x)
  derivative x := (f.derivative x).prod (g.derivative x)
  correct x := (f.correct x).prodMk (g.correct x)

def product (f : DMap E F) (g : DMap G H) : DMap (E × G) (F × H) :=
  pair (comp f fst) (comp g snd)

def add (f g : DMap E F) : DMap E F where
  primal x := f.primal x + g.primal x
  derivative x := f.derivative x + g.derivative x
  correct x := (f.correct x).add (g.correct x)

def neg (f : DMap E F) : DMap E F where
  primal x := -f.primal x
  derivative x := -f.derivative x
  correct x := (f.correct x).neg

def scale (s : ℝ) (f : DMap E F) : DMap E F where
  primal x := s • f.primal x
  derivative x := s • f.derivative x
  correct x := (f.correct x).const_smul s

/-- Nonlinear multiplication; the two derivative contributions are added. -/
def mul (f g : DMap E ℝ) : DMap E ℝ where
  primal x := f.primal x * g.primal x
  derivative x := f.primal x • g.derivative x + g.primal x • f.derivative x
  correct x := (f.correct x).mul (g.correct x)

theorem comp_assoc (h : DMap G H) (g : DMap F G) (f : DMap E F) :
    comp h (comp g f) = comp (comp h g) f := by ext x; rfl

theorem ident_comp (f : DMap E F) : comp ident f = f := by ext x; rfl
theorem comp_ident (f : DMap E F) : comp f ident = f := by ext x; rfl
theorem fst_pair (f : DMap E F) (g : DMap E G) : comp fst (pair f g) = f := by
  ext x
  rfl
theorem snd_pair (f : DMap E F) (g : DMap E G) : comp snd (pair f g) = g := by
  ext x
  rfl
theorem pair_eta (h : DMap E (F × G)) : pair (comp fst h) (comp snd h) = h := by
  apply DMap.ext
  intro x
  rfl

/-- The stored derivative is forced by the primal function, rather than chosen freely. -/
theorem derivative_eq_fderiv (f : DMap E F) (x : E) :
    f.derivative x = fderiv ℝ f.primal x := (f.correct x).fderiv.symm

end DMap

/-- Tangent data represents primal data by forgetting its tangent component. -/
def tangentRep (E : Type) : Squares.Rep where
  R := E × E
  S := E
  decode := Prod.fst

def tangent (f : DMap E F) (xv : E × E) : F × F :=
  (f.primal xv.1, f.derivative xv.1 xv.2)

def tangentSquare (f : DMap E F) : Squares.Square (tangentRep E) (tangentRep F) where
  impl := tangent f
  spec := f.primal
  commutes _ := rfl

/-- The second component is the analytic derivative applied to the input direction. -/
theorem tangent_correct (f : DMap E F) (x v : E) :
    (tangent f (x, v)).2 = fderiv ℝ f.primal x v := by
  exact congrArg (fun L : E →L[ℝ] F => L v) (f.derivative_eq_fderiv x)

theorem tangent_ident (xv : E × E) : tangent DMap.ident xv = xv := rfl

theorem tangent_comp (g : DMap F G) (f : DMap E F) (xv : E × E) :
    tangent (DMap.comp g f) xv = tangent g (tangent f xv) := rfl

theorem tangent_square_comp (g : DMap F G) (f : DMap E F) :
    tangentSquare (DMap.comp g f) = Squares.compose (tangentSquare g) (tangentSquare f) :=
  Squares.Square.ext (fun _ => rfl) (fun _ => rfl)

/-- Linear-map representations have ordinary functions as their denotations. -/
def linearRep (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Squares.Rep where
  R := E →L[ℝ] F
  S := E → F
  decode := fun L => L

def linearCompositionSquare : Squares.Square
    (Squares.product (linearRep F G) (linearRep E F)) (linearRep E G) where
  impl p := p.1.comp p.2
  spec p := p.1 ∘ p.2
  commutes _ := rfl

def linearPairSquare : Squares.Square
    (Squares.product (linearRep E F) (linearRep E G)) (linearRep E (F × G)) where
  impl p := p.1.prod p.2
  spec p := fun x => (p.1 x, p.2 x)
  commutes _ := rfl

end Applications.AD
