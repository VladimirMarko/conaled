import Applications.AD.Core
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Ring

/-!
# Changing the representation of a certified derivative

Forward mode postcomposes seed maps. Reverse mode precomposes covectors.
The continuation transformation is itself a continuous linear map; this is
proved by its construction from continuous bilinear composition. An arbitrary
function on covectors is never silently declared linear.

The author's errata (https://conal.net/papers/essence-of-ad/#errata-and-clarifications)
are incorporated in two ways: `onDot` returns an ordinary function, and the
proved `continuation_pair` equation explicitly turns forward pairing into
addition of reverse contributions.  Projection/injection equations similarly
reverse the cartesian/cocartesian roles.
-/

noncomputable section

namespace Applications.AD

variable {E F G R V : Type}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup R] [NormedSpace ℝ R]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Arbitrary seed spaces allow one direction, several directions, or the full Jacobian. -/
def forward (f : DMap E F) (x : E) (seed : V →L[ℝ] E) : F × (V →L[ℝ] F) :=
  (f.primal x, (f.derivative x).comp seed)

theorem forward_correct (f : DMap E F) (x : E) (seed : V →L[ℝ] E) (v : V) :
    (forward f x seed).2 v = fderiv ℝ f.primal x (seed v) := by
  exact congrArg (fun L : E →L[ℝ] F => L (seed v)) (f.derivative_eq_fderiv x)

theorem forward_comp (g : DMap F G) (f : DMap E F) (x : E) (seed : V →L[ℝ] E) :
    forward (DMap.comp g f) x seed =
      forward g (forward f x seed).1 (forward f x seed).2 := by
  rfl

theorem forward_identity_seed (f : DMap E F) (x : E) :
    forward f x (ContinuousLinearMap.id ℝ E) = (f.primal x, f.derivative x) := by
  rfl

/-- Elliott's continuation representation, with its linearity in the type. -/
abbrev Continuation (E F R : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup R] [NormedSpace ℝ R] :=
  (F →L[ℝ] R) →L[ℝ] (E →L[ℝ] R)

def continuation (L : E →L[ℝ] F) : Continuation E F R :=
  (ContinuousLinearMap.compL ℝ E F R).flip L

@[simp] theorem continuation_apply (L : E →L[ℝ] F) (k : F →L[ℝ] R) :
    continuation L k = k.comp L := rfl

theorem continuation_ident :
    continuation (ContinuousLinearMap.id ℝ E) =
      ContinuousLinearMap.id ℝ (E →L[ℝ] R) := by
  ext k x
  rfl

/-- Sequential order reverses. -/
theorem continuation_comp (L : E →L[ℝ] F) (M : F →L[ℝ] G) :
    (continuation (R := R) (M.comp L)) = (continuation L).comp (continuation M) := by
  ext k x
  rfl

/-- Reverse contributions from both outputs add at their common input. -/
theorem continuation_pair (L : E →L[ℝ] F) (M : E →L[ℝ] G)
    (k : (F × G) →L[ℝ] R) :
    continuation (L.prod M) k =
      continuation L (k.comp (ContinuousLinearMap.inl ℝ F G)) +
      continuation M (k.comp (ContinuousLinearMap.inr ℝ F G)) := by
  ext x
  change k (L x, M x) = k (L x, 0) + k (0, M x)
  rw [← k.map_add]
  simp

theorem continuation_fst (k : E →L[ℝ] R) (p : E × F) :
    continuation (ContinuousLinearMap.fst ℝ E F) k p = k p.1 := rfl

theorem continuation_snd (k : F →L[ℝ] R) (p : E × F) :
    continuation (ContinuousLinearMap.snd ℝ E F) k p = k p.2 := rfl

/-- A product projection's transpose inserts a zero in the unused input. -/
theorem continuation_inl (k : (E × F) →L[ℝ] R) (x : E) :
    continuation (ContinuousLinearMap.inl ℝ E F) k x = k (x, 0) := rfl

theorem continuation_inr (k : (E × F) →L[ℝ] R) (y : F) :
    continuation (ContinuousLinearMap.inr ℝ E F) k y = k (0, y) := rfl

def reverse (f : DMap E F) (x : E) : F × Continuation E F R :=
  (f.primal x, continuation (f.derivative x))

theorem reverse_correct (f : DMap E F) (x : E) (k : F →L[ℝ] R) (v : E) :
    (reverse f x).2 k v = k (fderiv ℝ f.primal x v) := by
  exact congrArg (fun L : E →L[ℝ] F => k (L v)) (f.derivative_eq_fderiv x)

theorem reverse_comp (g : DMap F G) (f : DMap E F) (x : E) :
    (reverse (R := R) (DMap.comp g f) x).2 =
      (reverse f x).2.comp (reverse g (f.primal x)).2 := by
  exact continuation_comp _ _

/-- The corrected `onDot` signature returns a function for an arbitrary argument `h`. -/
def onDot {A B DA DB : Type} (dotB : B → DB) (unDotA : DA → A)
    (h : DB → DA) : B → A := unDotA ∘ h ∘ dotB

section Hilbert

variable {EH FH GH : Type}
variable [NormedAddCommGroup EH] [NormedAddCommGroup FH] [NormedAddCommGroup GH]
variable [InnerProductSpace ℝ EH] [CompleteSpace EH]
variable [InnerProductSpace ℝ FH] [CompleteSpace FH]
variable [InnerProductSpace ℝ GH] [CompleteSpace GH]

/-- A Hilbert-space vector denotes its dot-product covector. -/
@[reducible] def dotRep (EH : Type) [NormedAddCommGroup EH] [InnerProductSpace ℝ EH] : Squares.Rep where
  R := EH
  S := EH →L[ℝ] ℝ
  decode := innerSL ℝ

/-- This square proves the dual representation, rather than assuming `onDot` is linear. -/
def adjointSquare (L : EH →L[ℝ] FH) : Squares.Square (dotRep FH) (dotRep EH) where
  impl := (ContinuousLinearMap.adjoint (𝕜 := ℝ) L : FH →L[ℝ] EH)
  spec k := continuation L k
  commutes y := by
    ext x
    exact ContinuousLinearMap.adjoint_inner_left L x y

theorem adjoint_square_comp (L : EH →L[ℝ] FH) (M : FH →L[ℝ] GH) :
    adjointSquare (M.comp L) = Squares.compose (adjointSquare L) (adjointSquare M) := by
  apply Squares.Square.ext
  · intro z
    exact congrArg (fun A : GH →L[ℝ] EH => A z) (ContinuousLinearMap.adjoint_comp M L)
  · intro k
    rfl

def gradient (f : DMap EH ℝ) (x : EH) : EH :=
  ContinuousLinearMap.adjoint (𝕜 := ℝ) (f.derivative x) (1 : ℝ)

/-- The returned gradient has the defining directional-derivative property. -/
theorem gradient_correct (f : DMap EH ℝ) (x v : EH) :
    @inner ℝ EH _ (gradient f x) v = fderiv ℝ f.primal x v := by
  calc
    @inner ℝ EH _ (gradient f x) v = @inner ℝ ℝ _ (1 : ℝ) (f.derivative x v) :=
      ContinuousLinearMap.adjoint_inner_left (f.derivative x) v (1 : ℝ)
    _ = f.derivative x v := by simp
    _ = fderiv ℝ f.primal x v := congrArg (fun L : EH →L[ℝ] ℝ => L v)
      (f.derivative_eq_fderiv x)

end Hilbert

/-! ## A nonlinear, two-input reverse calculation -/

def mixedPolynomial : DMap (ℝ × ℝ) ℝ :=
  DMap.add (DMap.mul DMap.fst DMap.fst) (DMap.mul DMap.fst DMap.snd)

theorem mixedPolynomial_primal (x y : ℝ) :
    mixedPolynomial.primal (x, y) = x * x + x * y := rfl

theorem mixedPolynomial_derivative (x y dx dy : ℝ) :
    mixedPolynomial.derivative (x, y) (dx, dy) = (2 * x + y) * dx + x * dy := by
  simp only [mixedPolynomial, DMap.add, DMap.mul, DMap.fst, DMap.snd, DMap.linear,
    add_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

theorem mixedPolynomial_reverse (x y dx dy : ℝ) :
    (reverse mixedPolynomial (x, y)).2 (ContinuousLinearMap.id ℝ ℝ) (dx, dy) =
      (2 * x + y) * dx + x * dy := mixedPolynomial_derivative x y dx dy

theorem mixedPolynomial_true_derivative (x y : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => p.1 * p.1 + p.1 * p.2)
      (mixedPolynomial.derivative (x, y)) (x, y) := mixedPolynomial.correct (x, y)

end Applications.AD
