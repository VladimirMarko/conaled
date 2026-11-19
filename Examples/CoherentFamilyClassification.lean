import SquareKit.Internal.RepresentableCoherentRecovery
import Examples.CategoryValuedEvaluation
import Examples.SharedRepresentableClassification
import Examples.NonCubicalClassification

/-! Coherent recovery with a nonidentity comparison, noninvertible morphisms,
and a rejection when restriction comparisons are not invertible. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CoherentFamilyClassification
open CategoryTheory CategoryTheory.Functor
open SquareKit.CoherentFamilyClassification
open SquareKit.RepresentableClassification
open Examples.CategoryValuedEvaluation

private def swap : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

private def twist (n : ℕ) : Bool ≃ Bool := if n % 2 = 0 then Equiv.refl _ else swap

/-- A family of Boolean presentations whose restrictions can swap the two values. -/
def twisted : ℕᵒᵖ ⥤ Type where
  obj _ := Bool
  map {m n} _ := TypeCat.ofHom (fun b => twist n.unop ((twist m.unop).symm b))
  map_id n := by ext b; exact (twist n.unop).apply_symm_apply b
  map_comp f g := by
    ext b
    dsimp
    rw [Equiv.symm_apply_apply]

instance twisted_map_isIso {m n : ℕᵒᵖ} (f : m ⟶ n) : IsIso (twisted.map f) := by
  change IsIso (((twist m.unop).symm.trans (twist n.unop)).toIso.hom)
  infer_instance

/-- Local data depends on its root; the coherent comparison need not be identity. -/
def localData : Code context.Elements (Type) :=
  ⟨Arrow.leftFunc ⋙ Functor.Elements.π context ⋙ twisted, fun {_ _} f _ => by
    change IsIso (twisted.map f.left.hom)
    infer_instance⟩

/-- The derived recovery genuinely uses the selected nonidentity restriction. -/
example : (recovery _ _ localData).hom.app (Arrow.mk step) false = true := rfl

example : (recovery _ _ localData).inv.app (Arrow.mk step) true = false := by
  have h := congrArg (fun f => f false) ((recovery _ _ localData).hom_inv_id_app (Arrow.mk step))
  exact h

/-- Decoding retains the original nonidentity family action. -/
example : ((decode _ _).obj localData).map step false = true := rfl

/-- A morphism between coherent diagrams need not be invertible. -/
def collapse : localData ⟶ (code context.Elements (Type)).obj ((Functor.const _).obj PUnit) :=
  ObjectProperty.homMk { app := fun _ => TypeCat.ofHom (fun _ => PUnit.unit) }

theorem collapse_not_iso : ¬ IsIso collapse := by
  intro h
  have : IsIso ((decode _ _).map collapse) := (decode _ _).map_isIso collapse
  have hi : IsIso (((decode _ _).map collapse).app (point 0)) := inferInstance
  have hinj := (CategoryTheory.isIso_iff_bijective _).mp hi |>.1
  have bad : (false : Bool) = true := hinj rfl
  contradiction

/-- Morphism recovery is the naturality square of the derived categorical equivalence. -/
example : collapse ≫ (equivalence _ _).unitIso.hom.app _ =
    (equivalence _ _).unitIso.hom.app localData ≫
      ((decode _ _ ⋙ code _ _).map collapse) :=
  (equivalence _ _).unitIso.hom.naturality collapse

/-- Actual represented restriction comparisons also exist for this non-strict code. -/
noncomputable def representedComparison :=
  CoherentFamily.localRestrictionIso (Type) localData step

/-- The categorical classification preserves noninvertible arrows as well. -/
example : ((decode _ _).obj ((code context.Elements ℕᵒᵖ).obj family)).map step =
    family.map step := rfl

/-- Dropping invertibility admits a local diagram that cannot recover its target view. -/
def badData : Arrow context.Elements ⥤ ℕᵒᵖ :=
  Arrow.leftFunc ⋙ Functor.Elements.π context

theorem badData_no_recovery :
    IsEmpty (badData.obj (Arrow.mk step) ≅ badData.obj ((identityArrow _).obj (point 1))) :=
  ⟨fun e => by
    have h := leOfHom e.inv.unop
    change 2 ≤ 1 at h
    omega⟩

theorem badData_not_coherent : ¬ Coherent context.Elements ℕᵒᵖ badData := by
  intro h
  have hi := h (evaluationArrow _ (Arrow.mk step)) (by
    change IsIso (𝟙 (point 1))
    infer_instance)
  exact badData_no_recovery.false (@asIso _ _ _ _ _ hi)

/-- Context substitution and its composite are covered for arbitrary coherent codes. -/
example {C : Type} [Category C] {Γ Δ Θ : Context.{0} C}
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (A : Code Γ.Elements (Type)) (x : Θ.Elements) :
    ((decodeReindex (τ ≫ σ).mapElements).hom.app A).app x =
      ((decodeReindex τ.mapElements).hom.app ((reindex σ.mapElements).obj A)).app x ≫
        ((decodeReindex σ.mapElements).hom.app A).app (τ.mapElements.obj x) :=
  decodeReindex_comp σ.mapElements τ.mapElements A x

namespace Substitution
open Examples.NonCubicalClassification

/-- A dependent, nonconstant family exercises two concrete context substitutions. -/
noncomputable def classified :=
  (CoherentFamily.classification (Type) Examples.NonCubicalClassification.context).inverse.obj
    Examples.NonCubicalClassification.family

example : ((decode _ _).obj
    ((reindex Examples.NonCubicalClassification.double.mapElements).obj
      ((reindex Examples.NonCubicalClassification.successor.mapElements).obj classified))).obj
        (Examples.NonCubicalClassification.point 2) = Fin 6 := rfl

example : ((decodeReindex (Examples.NonCubicalClassification.double ≫
    Examples.NonCubicalClassification.successor).mapElements).hom.app classified).app
      (Examples.NonCubicalClassification.point 2) =
    ((decodeReindex Examples.NonCubicalClassification.double.mapElements).hom.app
      ((reindex Examples.NonCubicalClassification.successor.mapElements).obj classified)).app
        (Examples.NonCubicalClassification.point 2) ≫
    ((decodeReindex Examples.NonCubicalClassification.successor.mapElements).hom.app classified).app
      (Examples.NonCubicalClassification.point 4) :=
  decodeReindex_comp Examples.NonCubicalClassification.successor.mapElements
    Examples.NonCubicalClassification.double.mapElements classified
    (Examples.NonCubicalClassification.point 2)

end Substitution

namespace NativeOriginal
universe u
variable {Γ : SquareKit.Cubical.Presheaf.Context.{u}}
  (A : SquareKit.Cubical.Presheaf.LocalFamily Γ)

example (x : Γ.Elements) :
    (CoherentFamily.localView (Type u) x).obj ((code Γ.Elements _).obj A.family) =
      (A.code.app x.obj ⟨x.val⟩).family := rfl

example : (Examples.SharedRepresentableClassification.Original.evaluation A).categorical.iso =
    A.decodeCodeIso :=
  (Examples.SharedRepresentableClassification.Original.evaluation A).categorical_iso.trans
    (Examples.SharedRepresentableClassification.Original.comparison_native A)
end NativeOriginal

namespace NativeCartesian
universe u
variable {Γ : SquareKit.Cubical.Cartesian.Context.{u}}
  (A : SquareKit.Cubical.Cartesian.LocalFamily Γ)

example (x : Γ.Elements) :
    (CoherentFamily.localView (Type u) x).obj ((code Γ.Elements _).obj A.family) =
      (A.code.app x.obj ⟨x.val⟩).family := rfl

example : (Examples.SharedRepresentableClassification.Target.evaluation A).categorical.iso =
    A.decodeCodeIso :=
  (Examples.SharedRepresentableClassification.Target.evaluation A).categorical_iso.trans
    (Examples.SharedRepresentableClassification.Target.comparison_native A)
end NativeCartesian

end Examples.CoherentFamilyClassification
