import SquareKit.Lawvere.Universal
import Examples.LawvereRecovery

/-! # Universal properties with constants, involution and addition

The equation constrains the unary symbol. The binary symbol has two independent
inputs. Doubling is a nonidentity homomorphism of the resulting integer model.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Examples.LawvereUniversal
open SquareKit SquareKit.Lawvere CategoryTheory

inductive Symbol | zero | neg | add

def arithmetic : Presentation where
  Symbol := Symbol
  arity
    | .zero => 0
    | .neg => 1
    | .add => 2
  Equation := Unit
  variableCount _ := 1
  lhs _ := .node .neg (fun _ => .node .neg (fun _ => .leaf 0))
  rhs _ := .leaf 0

def integers : arithmetic.EquationModel where
  Carrier := ℤ
  operation
    | .zero => fun _ => 0
    | .neg => fun x => -x (0 : Fin 1)
    | .add => fun x => x (0 : Fin 2) + x (1 : Fin 2)
  laws _ x := neg_neg (x (0 : Fin 1))

def doubling : integers ⟶ integers where
  toFun (x : ℤ) := 2 * x
  operation s x := by
    cases s <;> dsimp [integers] <;> ring

def zeroOp : arithmetic.operations.Op 0 := arithmetic.symbol .zero
def negOp : arithmetic.operations.Op 1 := arithmetic.symbol .neg
def addOp : arithmetic.operations.Op 2 := arithmetic.symbol .add

example : integers.toAlgebra.act zeroOp Fin.elim0 = (0 : ℤ) := rfl
example : integers.toAlgebra.act negOp (fun _ => (3 : ℤ)) = (-3 : ℤ) := rfl
example : integers.toAlgebra.act addOp ![(3 : ℤ), (4 : ℤ)] = (7 : ℤ) := rfl

/-- The functor on models carries the binary calculation and the nonidentity map. -/
example : ((arithmetic.equationModelEquivalence.functor.map doubling).app ⟨1⟩)
    (fun _ => integers.toAlgebra.act addOp ![(3 : ℤ), (4 : ℤ)]) 0 = (14 : ℤ) := rfl

example : (arithmetic.equationModelEquivalence.functor.map (doubling ≫ doubling)).app ⟨1⟩
    (fun _ => (3 : ℤ)) 0 = (12 : ℤ) := rfl

example : (arithmetic.equationUnitIso.hom.app integers).toFun (3 : ℤ) = (3 : ℤ) := rfl

/-- Naturality retains the homomorphism through primitive-operation recovery. -/
example : doubling ≫ arithmetic.equationUnitIso.hom.app integers =
    arithmetic.equationUnitIso.hom.app integers ≫
      (Presentation.EquationModel.algebraFunctor ⋙ arithmetic.equationModelFunctor).map doubling :=
  arithmetic.equationUnitIso.hom.naturality doubling

/-- A model with nonliteral finite powers is recovered through the same equivalence. -/
example (M : Model arithmetic.operations.theory (Type)) :
    arithmetic.equationModelEquivalence.functor.obj
      (arithmetic.equationModelEquivalence.inverse.obj M) ≅ M :=
  arithmetic.equationModelEquivalence.counitIso.app M

/-- Primitive symbols can also be assigned to smooth operations of all three arities. -/
def smoothAssignment : arithmetic.Assignment smoothOperations where
  op
    | .zero => SmoothAlgebra.constant 0 0
    | .neg => ⟨fun x => -x (0 : Fin 1), (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).neg⟩
    | .add => ⟨fun x => x (0 : Fin 2) + x (1 : Fin 2),
        (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 0).add (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 1)⟩
  laws _ := by
    apply Subtype.ext
    funext x
    exact neg_neg (x (0 : Fin 1))

example (s : Symbol) :
    (arithmetic.assignmentEquiv smoothOperations smoothAssignment).map (arithmetic.symbol s) =
      smoothAssignment.op s := arithmetic.interpretation_symbol smoothAssignment s

example (F : arithmetic.operations.Map smoothOperations)
    (h : ∀ s, F.map (arithmetic.symbol s) = smoothAssignment.op s) :
    F = arithmetic.assignmentEquiv smoothOperations smoothAssignment :=
  arithmetic.interpretation_unique smoothAssignment F h

/-- Existing direct clients retain their original assumptions. -/
example (e : Examples.Lawvere.pointedInvolution.Equation) :
    Examples.Lawvere.pointedInvolution.evaluate Examples.Lawvere.smoothSymbol
        (Examples.Lawvere.pointedInvolution.lhs e) =
      Examples.Lawvere.pointedInvolution.evaluate Examples.Lawvere.smoothSymbol
        (Examples.Lawvere.pointedInvolution.rhs e) := Examples.Lawvere.smoothEquation e

open Examples.LawvereRecovery in
def toTagged : Hom smoothOperations.theory taggedTheory where
  toFunctor := forgetTag.asEquivalence.inverse
  preserves := inferInstance
  generatorIso := forgetTag.preimageIso (forgetTag.asEquivalence.counitIso.app ⟨1⟩)

def taggedInterpretation : Hom arithmetic.operations.theory Examples.LawvereRecovery.taggedTheory :=
  Hom.comp (arithmetic.assignmentEquiv smoothOperations smoothAssignment).theoryHom toTagged

/-- This interpretation lands in genuinely distinct but isomorphic tagged objects. -/
example : taggedInterpretation.toFunctor ≅
    (arithmetic.categoricalInterpretation (arithmetic.categoricalAssignment taggedInterpretation)).toFunctor :=
  arithmetic.categoricalUniqueness _ taggedInterpretation rfl

example : (Operations.normalizationIso taggedInterpretation).hom.app ⟨1⟩ ≫
    Examples.LawvereRecovery.taggedTheory.generatorIso.hom = taggedInterpretation.generatorIso.hom :=
  Operations.normalization_generator taggedInterpretation

/-- An increment does not satisfy the unary equation, even with legal arities. -/
def badOperation : (s : arithmetic.Symbol) → (Fin (arithmetic.arity s) → ℤ) → ℤ
  | .zero => fun _ => 0
  | .neg => fun x => x (0 : Fin 1) + 1
  | .add => fun x => x (0 : Fin 2) + x (1 : Fin 2)

example : ¬ ∀ e (x : Fin (arithmetic.variableCount e) → ℤ),
    FinitaryTerm.fold badOperation x (arithmetic.lhs e) =
      FinitaryTerm.fold badOperation x (arithmetic.rhs e) := by
  intro h
  have hzero := h () (fun _ => 0)
  change (0 : ℤ) + 1 + 1 = 0 at hzero
  norm_num at hzero

end Examples.LawvereUniversal
