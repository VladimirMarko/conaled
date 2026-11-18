import SquareKit.Lawvere.UnaryCombinations
import Examples.LawvereUniversal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Examples.LawvereCombinations
open SquareKit SquareKit.Lawvere CategoryTheory

def endomorphisms (X : Type) : Operations where
  Op n := (Fin n → X) → X
  var i x := x i
  subst f σ x := f (fun i => σ i x)
  var_subst _ _ := rfl
  subst_var _ := rfl
  subst_assoc _ _ _ := rfl

def free (arity : Nat) : Presentation where
  Symbol := Unit
  arity _ := arity
  Equation := PEmpty
  variableCount := PEmpty.elim
  lhs e := PEmpty.elim e
  rhs e := PEmpty.elim e

def addAssignment : (free 2).Assignment (endomorphisms ℤ) where
  op _ x := x (0 : Fin 2) + x (1 : Fin 2)
  laws e := PEmpty.elim e

theorem add_commutes : Operations.Commutes (addAssignment.op ()) (addAssignment.op ()) := by
  intro k x
  funext v
  change (x (0 : Fin 2) (0 : Fin 2) v + x (0 : Fin 2) (1 : Fin 2) v) + (x (1 : Fin 2) (0 : Fin 2) v + x (1 : Fin 2) (1 : Fin 2) v) =
    (x (0 : Fin 2) (0 : Fin 2) v + x (1 : Fin 2) (0 : Fin 2) v) + (x (0 : Fin 2) (1 : Fin 2) v + x (1 : Fin 2) (1 : Fin 2) v)
  omega

def addTensorAssignment : (Presentation.tensor (free 2) (free 2)).Assignment (endomorphisms ℤ) :=
  (Presentation.tensorAssignmentEquiv _ _ _).symm
    ⟨(addAssignment,addAssignment), fun _ _ => add_commutes⟩

def addTensor : (Presentation.tensor (free 2) (free 2)).operations.Map (endomorphisms ℤ) :=
  (Presentation.assignmentEquiv _ _) addTensorAssignment

example : addTensor.map ((Presentation.tensor (free 2) (free 2)).symbol (.inl ())) ![3,4] = 7 := by
  change ((Presentation.tensor (free 2) (free 2)).interpretation addTensorAssignment.op addTensorAssignment.laws).map _ _ = _
  rw [Presentation.interpretation_symbol]
  rfl

/-- The binary interchange equation is exercised on a nonconstant rectangle. -/
example : (endomorphisms ℤ).subst (addAssignment.op ())
    (fun i => (endomorphisms ℤ).subst (addAssignment.op ())
      (fun j => (fun _ : Fin 0 → ℤ => (![![1,2],![3,4]] : Fin 2 → Fin 2 → ℤ) i j)))
    Fin.elim0 = 10 := rfl

def increment : (free 1).Assignment (endomorphisms ℤ) := ⟨fun _ x => x (0 : Fin 1) + 1, fun e => PEmpty.elim e⟩
def double : (free 1).Assignment (endomorphisms ℤ) := ⟨fun _ x => 2 * x (0 : Fin 1), fun e => PEmpty.elim e⟩

def separateSum : (Presentation.sum (free 1) (free 1)).operations.Map (endomorphisms ℤ) :=
  (Presentation.sumMapEquiv _ _ _).symm
    ((Presentation.assignmentEquiv _ _) increment, (Presentation.assignmentEquiv _ _) double)

theorem increment_double_not_commute : ¬ Operations.Commutes (increment.op ()) (double.op ()) := by
  intro h
  have hh := congrFun (h 0 (fun _ _ _ => (0 : ℤ))) Fin.elim0
  change (1 : ℤ) = 2 at hh
  norm_num at hh

theorem no_tensor_extension : ¬ ∃ F : (Presentation.tensor (free 1) (free 1)).operations.Map (endomorphisms ℤ),
    F.map ((Presentation.tensor (free 1) (free 1)).symbol (.inl ())) = increment.op () ∧
    F.map ((Presentation.tensor (free 1) (free 1)).symbol (.inr ())) = double.op () := by
  rintro ⟨F,hf,hg⟩
  have h := (Presentation.tensorMapEquiv _ _ _ F).property 1 1 ((free 1).symbol ()) ((free 1).symbol ())
  rw [Presentation.tensorMapEquiv_apply] at h
  change Operations.Commutes (F.map ((Presentation.tensorInl _ _).map _))
    (F.map ((Presentation.tensorInr _ _).map _)) at h
  rw [Presentation.tensorInl_symbol, Presentation.tensorInr_symbol, hf, hg] at h
  exact increment_double_not_commute h

/-- Existing theories need no hand-authored presentation. -/
example (O R A : Operations) : (Operations.sum O R).Map A ≃ O.Map A × R.Map A :=
  Operations.sumMapEquiv O R A

/-- Nonskeletal interpretations have the same generator-compatible uniqueness comparison. -/
example (a : (Presentation.sum (free 2) (free 1)).Assignment Examples.LawvereRecovery.taggedTheory.operations)
    (F : Hom (Presentation.sum (free 2) (free 1)).operations.theory Examples.LawvereRecovery.taggedTheory)
    (h : (Presentation.sum (free 2) (free 1)).categoricalAssignment F = a) :
    F.toFunctor ≅ ((Presentation.sum (free 2) (free 1)).categoricalInterpretation a).toFunctor :=
  Presentation.categoricalUniqueness _ a F h
end Examples.LawvereCombinations

namespace Examples.LawvereCombinations
open SquareKit SquareKit.Lawvere CategoryTheory

def zeroAssignment : (free 0).Assignment (endomorphisms ℤ) := ⟨fun _ _ => 0, fun e => PEmpty.elim e⟩

def zeroTensorAssignment : (Presentation.tensor (free 0) (free 0)).Assignment (endomorphisms ℤ) :=
  (Presentation.tensorAssignmentEquiv _ _ _).symm
    ⟨(zeroAssignment,zeroAssignment), fun _ _ _ _ => rfl⟩

example : ((Presentation.tensor (free 0) (free 0)).assignmentEquiv _ zeroTensorAssignment).map
    ((Presentation.tensor (free 0) (free 0)).symbol (.inr ())) Fin.elim0 = 0 := by
  change ((Presentation.tensor (free 0) (free 0)).interpretation zeroTensorAssignment.op zeroTensorAssignment.laws).map _ _ = _
  rw [Presentation.interpretation_symbol]
  rfl

/-- Two different constants cannot commute: empty rectangles still impose an equation. -/
example : ¬ @Operations.Commutes (endomorphisms ℤ) 0 0 (fun _ => 0) (fun _ => 1) := by
  intro h
  have hh := congrFun (h 0 Fin.elim0) Fin.elim0
  change (0 : ℤ) = 1 at hh
  norm_num at hh

example : (Presentation.sumInl (free 1) (free 1)).comp separateSum =
    (free 1).assignmentEquiv _ increment := by
  have h := (Presentation.sumMapEquiv (free 1) (free 1) (endomorphisms ℤ)).apply_symm_apply
    ((free 1).assignmentEquiv _ increment, (free 1).assignmentEquiv _ double)
  rw [Presentation.sumMapEquiv_apply] at h
  exact congrArg Prod.fst h

open Examples.LawvereUniversal in
def smoothSumAssignment : (Presentation.sum arithmetic arithmetic).Assignment smoothOperations :=
  (Presentation.sumAssignmentEquiv _ _ _).symm (smoothAssignment,smoothAssignment)

open Examples.LawvereUniversal in
def taggedSum : Hom (Presentation.sum arithmetic arithmetic).operations.theory
    Examples.LawvereRecovery.taggedTheory :=
  Hom.comp ((Presentation.sum arithmetic arithmetic).assignmentEquiv _ smoothSumAssignment).theoryHom toTagged

example : taggedSum.toFunctor ≅
    ((Presentation.sum Examples.LawvereUniversal.arithmetic Examples.LawvereUniversal.arithmetic).categoricalInterpretation
      ((Presentation.sum Examples.LawvereUniversal.arithmetic Examples.LawvereUniversal.arithmetic).categoricalAssignment taggedSum)).toFunctor :=
  Presentation.categoricalUniqueness _ _ taggedSum rfl

example : (Operations.normalizationIso taggedSum).hom.app ⟨1⟩ ≫
    Examples.LawvereRecovery.taggedTheory.generatorIso.hom = taggedSum.generatorIso.hom :=
  Operations.normalization_generator taggedSum
end Examples.LawvereCombinations
