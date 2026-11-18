import SquareKit.Lawvere.Restriction
import Examples.LawvereUniversal
/-! # Restriction of constants, binary operations and model transformations

A nonidentity interpretation erases involution while retaining zero and addition.
Composed restriction checks recovery on operations and a doubling homomorphism.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Examples.LawvereRestriction
open SquareKit SquareKit.Lawvere SquareKit.Lawvere.Operations CategoryTheory
open Examples.LawvereUniversal

def eraseNegAssignment : arithmetic.Assignment arithmetic.operations where
  op
    | .zero => arithmetic.symbol .zero
    | .neg => arithmetic.operations.var (0 : Fin 1)
    | .add => arithmetic.symbol .add
  laws _ := by
    change arithmetic.operations.subst (arithmetic.operations.var (0 : Fin 1))
      (fun _ => arithmetic.operations.subst (arithmetic.operations.var (0 : Fin 1))
        (fun _ => arithmetic.operations.var (0 : Fin 1))) = arithmetic.operations.var (0 : Fin 1)
    rw [Operations.var_subst, Operations.var_subst]

def eraseNeg : arithmetic.operations.Map arithmetic.operations :=
  arithmetic.assignmentEquiv arithmetic.operations eraseNegAssignment

@[simp] theorem eraseNeg_symbol (s : Symbol) : eraseNeg.map (arithmetic.symbol s) = eraseNegAssignment.op s :=
  arithmetic.interpretation_symbol eraseNegAssignment s

theorem eraseNeg_ne_id : eraseNeg ≠ Map.id arithmetic.operations := by
  intro h
  have he := congrArg (fun F : arithmetic.operations.Map arithmetic.operations =>
    integers.toAlgebra.act (F.map (arithmetic.symbol .neg)) (fun _ => (1 : ℤ))) h
  rw [eraseNeg_symbol] at he
  change (1 : ℤ) = -1 at he
  norm_num at he

/-- Constants and a genuine binary operation survive composed restriction and recovery. -/
example : (Recovery.algebra ((Model.restrict eraseNeg.theoryHom).obj
    ((Model.restrict eraseNeg.theoryHom).obj integers.toAlgebra.model))).act
      zeroOp Fin.elim0 (0 : Fin 1) = (0 : ℤ) := by
  rw [Recovery.act_restrict, Recovery.act_restrict]
  simp only [zeroOp, eraseNeg_symbol, eraseNegAssignment]
  rw [Algebra.recovered_act]
  rfl

example : (Recovery.algebra ((Model.restrict eraseNeg.theoryHom).obj
    ((Model.restrict eraseNeg.theoryHom).obj integers.toAlgebra.model))).act
      addOp (fun i _ => (![3, 4] : Fin 2 → ℤ) i) (0 : Fin 1) = (7 : ℤ) := by
  rw [Recovery.act_restrict, Recovery.act_restrict]
  simp only [addOp, eraseNeg_symbol, eraseNegAssignment]
  rw [Algebra.recovered_act]
  rfl

/-- A nonidentity model map is retained by restriction and recovery. -/
example : (Recovery.functor.map ((Model.restrict (eraseNeg.comp eraseNeg).theoryHom).map
    (arithmetic.equationModelEquivalence.functor.map doubling))).toFun
      (fun _ => (3 : ℤ)) (0 : Fin 1) = (6 : ℤ) := by
  rw [Recovery.functor_map_apply]
  rfl

example (M : Model arithmetic.operations.theory (Type)) :
    Recovery.restrictionIso (eraseNeg.comp eraseNeg) M =
      (Algebra.restrict eraseNeg).mapIso (Recovery.restrictionIso eraseNeg M) ≪≫
        Recovery.restrictionIso eraseNeg ((Model.restrict eraseNeg.theoryHom).obj M) :=
  Recovery.restrictionIso_comp eraseNeg eraseNeg M

/-- Full functor laws apply to arbitrary targets and arbitrary model transformations. -/
example {T U V : Theory.{u,v}} {C : Type w} [Category.{z} C]
    (F : Hom T U) (G : Hom U V) :
    Model.restrict (C := C) (F.comp G) = Model.restrict G ⋙ Model.restrict F :=
  Model.restrict_comp F G

example {T U V : Theory.{u,v}} {C : Type w} [Category.{z} C]
    (F : Hom T U) (G : Hom U V) {M N : Model V C} (η : M ⟶ N) (X : T.Obj) :
    ((Model.restrict (F.comp G)).map η).app X =
      ((Model.restrict F).map ((Model.restrict G).map η)).app X := rfl

/-- The chosen-generator comparison survives the tagged nonskeletal target. -/
example (M : Model Examples.LawvereRecovery.taggedTheory (Type))
    (x : M.toFunctor.obj Examples.LawvereRecovery.taggedTheory.generator) :
    ((Model.originalRestrictionComparison arithmetic.operations.theory taggedInterpretation).hom.app M).toFun x =
      M.toFunctor.map taggedInterpretation.generatorIso.inv x :=
  Model.originalRestrictionComparison_apply _ _ _ _

example {T U V : Theory.{u,v}} (F : Hom T U) (G : Hom U V) (M : Model V (Type w))
    (x : M.toFunctor.obj V.generator) :
    ((Model.originalRestrictionComparison T (F.comp G)).hom.app M).toFun x =
      ((Model.originalRestrictionComparison T F).hom.app ((Model.restrict G).obj M)).toFun
        (((Model.originalRestrictionComparison U G).hom.app M).toFun x) :=
  Model.originalRestrictionComparison_comp_apply T F G M x

end Examples.LawvereRestriction
