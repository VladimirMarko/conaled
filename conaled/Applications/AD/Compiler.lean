import Applications.AD.Modes
import FirstOrder

/-!
# A differentiated interpretation of the existing first-order compiler

The source syntax and compiler are the unchanged `FirstOrderCompiler` library.
Every object is interpreted by its real normed space, including the zero-
dimensional terminal object and arbitrarily nested products.  The target
constructs `DMap`s.  Primitive derivatives are discharged locally; the global
theorem then applies to every term, every context, and every environment.

The theorem includes an actual Fréchet derivative of the independent source
evaluator. It does not merely prove that the primal result was preserved.
-/

noncomputable section

namespace Applications.AD.FirstOrder

instance valNormedAddCommGroup : (a : FirstOrderCompiler.Ty) → NormedAddCommGroup (FirstOrderCompiler.Val ℝ a)
  | .base => inferInstance
  | .unit => inferInstance
  | .prod a b =>
    letI := valNormedAddCommGroup a
    letI := valNormedAddCommGroup b
    inferInstance

instance valNormedSpace : (a : FirstOrderCompiler.Ty) → NormedSpace ℝ (FirstOrderCompiler.Val ℝ a)
  | .base => inferInstance
  | .unit => inferInstance
  | .prod a b =>
    letI := valNormedSpace a
    letI := valNormedSpace b
    inferInstance

variable {Prim : FirstOrderCompiler.Ty → FirstOrderCompiler.Ty → Type}

abbrev PrimitiveD (Prim : FirstOrderCompiler.Ty → FirstOrderCompiler.Ty → Type) :=
  {a b : FirstOrderCompiler.Ty} → Prim a b → DMap (FirstOrderCompiler.Val ℝ a) (FirstOrderCompiler.Val ℝ b)

def meaning (P : PrimitiveD Prim) {a b : FirstOrderCompiler.Ty} (p : Prim a b) :
    FirstOrderCompiler.Val ℝ a → FirstOrderCompiler.Val ℝ b := (P p).primal

def target (P : PrimitiveD Prim) : FirstOrderCompiler.Target Prim where
  Hom a b := DMap (FirstOrderCompiler.Val ℝ a) (FirstOrderCompiler.Val ℝ b)
  ident := DMap.ident
  comp := DMap.comp
  terminal := DMap.constant ()
  fst := DMap.fst
  snd := DMap.snd
  pair := DMap.pair
  primitive := P

def sound (P : PrimitiveD Prim) : FirstOrderCompiler.Sound ℝ (target P) (meaning P) where
  denote f := f.primal
  ident _ := rfl
  comp _ _ _ := rfl
  terminal _ := rfl
  fst _ := rfl
  snd _ := rfl
  pair _ _ _ := rfl
  primitive _ _ := rfl

def compile (P : PrimitiveD Prim) (t : FirstOrderCompiler.Term Prim Γ a) :
    DMap (FirstOrderCompiler.Val ℝ (FirstOrderCompiler.context Γ)) (FirstOrderCompiler.Val ℝ a) := FirstOrderCompiler.compile (target P) t

theorem compile_primal (P : PrimitiveD Prim) (t : FirstOrderCompiler.Term Prim Γ a)
    (ρ : FirstOrderCompiler.Val ℝ (FirstOrderCompiler.context Γ)) :
    (compile P t).primal ρ = FirstOrderCompiler.eval (meaning P) t ρ :=
  FirstOrderCompiler.compile_sound (target P) (sound P) t ρ

/-- Global derivative preservation for the independent source denotation. -/
theorem compile_hasFDerivAt (P : PrimitiveD Prim) (t : FirstOrderCompiler.Term Prim Γ a)
    (ρ : FirstOrderCompiler.Val ℝ (FirstOrderCompiler.context Γ)) :
    HasFDerivAt (FirstOrderCompiler.eval (meaning P) t) ((compile P t).derivative ρ) ρ := by
  have heq : (compile P t).primal = FirstOrderCompiler.eval (meaning P) t := funext (compile_primal P t)
  rw [← heq]
  exact (compile P t).correct ρ

theorem compile_derivative (P : PrimitiveD Prim) (t : FirstOrderCompiler.Term Prim Γ a)
    (ρ v : FirstOrderCompiler.Val ℝ (FirstOrderCompiler.context Γ)) :
    (compile P t).derivative ρ v = fderiv ℝ (FirstOrderCompiler.eval (meaning P) t) ρ v := by
  exact congrArg (fun L : FirstOrderCompiler.Val ℝ (FirstOrderCompiler.context Γ) →L[ℝ] FirstOrderCompiler.Val ℝ a => L v)
    (compile_hasFDerivAt P t ρ).fderiv.symm

theorem compile_forward (P : PrimitiveD Prim) (t : FirstOrderCompiler.Term Prim Γ a)
    (ρ v : FirstOrderCompiler.Val ℝ (FirstOrderCompiler.context Γ)) :
    tangent (compile P t) (ρ, v) =
      (FirstOrderCompiler.eval (meaning P) t ρ, fderiv ℝ (FirstOrderCompiler.eval (meaning P) t) ρ v) := by
  exact Prod.ext (compile_primal P t ρ) (compile_derivative P t ρ v)

theorem compile_reverse (P : PrimitiveD Prim) (t : FirstOrderCompiler.Term Prim Γ a)
    (ρ v : FirstOrderCompiler.Val ℝ (FirstOrderCompiler.context Γ)) (k : FirstOrderCompiler.Val ℝ a →L[ℝ] ℝ) :
    (reverse (compile P t) ρ).2 k v = k (fderiv ℝ (FirstOrderCompiler.eval (meaning P) t) ρ v) := by
  exact congrArg k (compile_derivative P t ρ v)

/-! ## Discharged arithmetic primitives and a compiled example -/

inductive RealPrim : FirstOrderCompiler.Ty → FirstOrderCompiler.Ty → Type where
  | constant : ℝ → RealPrim .unit .base
  | add : RealPrim (.prod .base .base) .base
  | mul : RealPrim (.prod .base .base) .base

def realPrimitives : PrimitiveD RealPrim
  | _, _, .constant c => DMap.constant c
  | _, _, .add => DMap.add DMap.fst DMap.snd
  | _, _, .mul => DMap.mul DMap.fst DMap.snd

def inputX : FirstOrderCompiler.Term RealPrim [.prod .base .base] .base := .fst (.var .here)
def inputY : FirstOrderCompiler.Term RealPrim [.prod .base .base] .base := .snd (.var .here)

/-- Let-sharing plus nonlinear multiplication: let z = x*y in z*z+x. -/
def sharedPolynomial : FirstOrderCompiler.Term RealPrim [.prod .base .base] .base :=
  .letE (.prim .mul (.pair inputX inputY))
    (.prim .add (.pair (.prim .mul (.pair (.var .here) (.var .here)))
      (.fst (.var (.there .here)))))

theorem sharedPolynomial_primal (x y : ℝ) :
    (compile realPrimitives sharedPolynomial).primal ((), (x, y)) =
      (x * y) * (x * y) + x := rfl

theorem sharedPolynomial_derivative (x y dx dy : ℝ) :
    (compile realPrimitives sharedPolynomial).derivative ((), (x, y)) ((), (dx, dy)) =
      (2 * x * y * y + 1) * dx + (2 * x * x * y) * dy := by
  change (x * y) * (x * dy + y * dx) + (x * y) * (x * dy + y * dx) + dx = _
  ring

theorem sharedPolynomial_reverse (x y dx dy : ℝ) :
    (reverse (compile realPrimitives sharedPolynomial) ((), (x, y))).2
        (ContinuousLinearMap.id ℝ ℝ) ((), (dx, dy)) =
      (2 * x * y * y + 1) * dx + (2 * x * x * y) * dy :=
  sharedPolynomial_derivative x y dx dy

end Applications.AD.FirstOrder
