import SquareKit.Lawvere.Concrete

/-! Checked clients of the common categorical API. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Examples.Lawvere
open SquareKit SquareKit.Lawvere CategoryTheory CategoryTheory.Limits

/-- A presentation with a constant and an involutive unary operation. -/
inductive Symbol where | zero | neg deriving DecidableEq

abbrev pointedInvolution : Presentation where
  Symbol := Symbol
  arity | .zero => 0 | .neg => 1
  Equation := Unit
  variableCount _ := 1
  lhs _ := .node .neg (fun _ => .node .neg (fun _ => .leaf 0))
  rhs _ := .leaf 0

def smoothSymbol : (s : Symbol) → smoothOperations.Op (pointedInvolution.arity s)
  | .zero => SmoothAlgebra.constant 0 0
  | .neg => ⟨fun x => -x 0, (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).neg⟩

theorem smoothEquation (e : pointedInvolution.Equation) :
    pointedInvolution.evaluate smoothSymbol (pointedInvolution.lhs e) =
      pointedInvolution.evaluate smoothSymbol (pointedInvolution.rhs e) := by
  apply Subtype.ext
  funext x
  exact neg_neg (x 0)

noncomputable abbrev toSmooth : Hom pointedInvolution.operations.theory smoothOperations.theory :=
  (pointedInvolution.interpretation smoothSymbol smoothEquation).theoryHom

noncomputable abbrev realModel : Model pointedInvolution.operations.theory (Type) :=
  (Model.restrict toSmooth).obj (smoothAlgebra ℝ).model

/-- A genuine change of theory recovers the expected real operation. -/
example (x : Fin 1 → ℝ) :
    realModel.toFunctor.map
      (fun _ : Fin 1 => Quotient.mk (pointedInvolution.setoid 1)
        (.node .neg (fun _ => .leaf 0))) x (0 : Fin 1) = -x 0 := rfl

/-- Nullary operations are interpreted on the empty context. -/
example (x : Fin 0 → ℝ) :
    realModel.toFunctor.map
      (fun _ : Fin 1 => Quotient.mk (pointedInvolution.setoid 0)
        (.node .zero Fin.elim0)) x (0 : Fin 1) = (0 : ℝ) := rfl

/-- The equation becomes equality of open operations in the theory. -/
example :
    Quotient.mk (pointedInvolution.setoid 1) (pointedInvolution.lhs ()) =
      Quotient.mk (pointedInvolution.setoid 1) (.leaf 0) :=
  Quotient.sound (.equation ())

/-- Composition means first increment, then double: at three the answer is eight. -/
def increment : (⟨1⟩ : smoothOperations.Context) ⟶ ⟨1⟩ :=
  fun _ => ⟨fun x => x 0 + 1, (contDiff_apply ℝ (fun _ => ℝ) 0).add contDiff_const⟩
def double : (⟨1⟩ : smoothOperations.Context) ⟶ ⟨1⟩ :=
  fun _ => ⟨fun x => 2 * x 0, contDiff_const.mul (contDiff_apply ℝ (fun _ => ℝ) 0)⟩

example : (smoothAlgebra ℝ).model.toFunctor.map (increment ≫ double) (fun _ => (3 : ℝ)) (0 : Fin 1) = (8 : ℝ) := by
  rw [Functor.map_comp]
  change (2 : ℝ) * (3 + 1) = 8
  norm_num

/-- The empty context has the universal property, even in theories without constants. -/
example : IsLimit (DeMorgan.operations.powerFan 0) := DeMorgan.operations.powerLimit 0
example : PreservesFiniteProducts realModel.toFunctor := inferInstance

/-- Existing smooth freeness remains available alongside the categorical API. -/
example (n : Nat) : SmoothAlgebra.Hom (SmoothAlgebra.Free n) ℝ ≃ (Fin n → ℝ) :=
  SmoothAlgebra.freeEquiv n

example (a b : Cubical.Cube) :
    (a ⟶ b) ≃ ((⟨a.dimension⟩ : DeMorgan.operations.Context) ⟶ ⟨b.dimension⟩) :=
  DeMorgan.cubeHomEquiv a b
example : Quotient.mk (DeMorgan.termSetoid 1) (.meet (.var 0) (.neg (.var 0))) ≠
    Quotient.mk (DeMorgan.termSetoid 1) .zero := DeMorgan.not_boolean

/-- Model homomorphisms retain the original smooth maps. -/
example (h : SmoothAlgebra.Hom ℝ ℝ) (n : smoothOperations.Context) (x : Fin n.size → ℝ)
    (i : Fin n.size) : (smoothHom h).app n x i = h (x i) := rfl
/-- The generic models are not restricted to the category of types. -/
def tautological (T : Theory) : Model T T.Obj := ⟨𝟭 _, inferInstance⟩

/-- Recover an existing unary word model through guarded soundness and the clone. -/
def unaryInvolution : UnaryInteraction.Presentation Unit where
  Law := Unit
  lhs _ := [(), ()]
  rhs _ := []

def boolUnary : GuardedTheory.Model (unaryPresentation unaryInvolution).guarded :=
  unaryModel unaryInvolution (fun _ x => !x) (by intro e x; cases x <;> rfl)

noncomputable def boolModel := ((unaryPresentation unaryInvolution).algebra boolUnary).model

example : boolModel.toFunctor.map
    (fun _ : Fin 1 => Quotient.mk ((unaryPresentation unaryInvolution).setoid 1)
      (UnaryInteraction.term [()])) (fun _ => true) (0 : Fin 1) = false := rfl

example (T : Theory) (M : Model T (Type)) :
    ((Model.restrict (Hom.id T)).obj M).toFunctor = M.toFunctor := Model.restrict_id_obj M

example {T U V : Theory} (F : Hom T U) (G : Hom U V) (M : Model V (Type)) :
    ((Model.restrict (F.comp G)).obj M).toFunctor =
      ((Model.restrict F).obj ((Model.restrict G).obj M)).toFunctor :=
  Model.restrict_comp_obj F G M

end Examples.Lawvere
