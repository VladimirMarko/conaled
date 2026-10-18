import SquareKit.SmoothLocalization
import Applications.AD.SmoothAlgebras

/-! Experimental real and first-order infinitesimal points of smooth localization.
Real-point agreement alone makes no claim about algebras of functions on an open set. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.Localization
open scoped ContDiff
variable {n : ℕ}
variable {B : Type*} [CommRing B] [Algebra ℝ B] [Structure B]

def pointEquiv (f : Free n) : Hom (Principal f) B ≃ {x : Fin n → B // IsUnit (evaluate x f)} :=
  (principalHomEquiv f).trans {
    toFun := fun h => ⟨freeEquiv n h.val, by
      change IsUnit (evaluate (fun i => h.val (generator i)) f)
      rw [evaluate_unique]; exact h.property⟩
    invFun := fun x => ⟨evaluate x.val, x.property⟩
    left_inv := fun h => Subtype.ext (evaluate_unique h.val)
    right_inv := fun x => Subtype.ext ((freeEquiv n).right_inv x.val) }

def realPoints (f : Free n) : Hom (Principal f) ℝ ≃ {x : Fin n → ℝ // f.val x ≠ 0} :=
  (pointEquiv f).trans {
    toFun := fun x => ⟨x.val, isUnit_iff_ne_zero.mp x.property⟩
    invFun := fun x => ⟨x.val, isUnit_iff_ne_zero.mpr x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem real_inverse (f : Free n) (x : {x : Fin n → ℝ // f.val x ≠ 0}) :
    (realPoints f).symm x (inverse f) = 1 / f.val x.val := by
  change principalLift f (evaluate x.val) (isUnit_iff_ne_zero.mpr x.property) (inverse f) = _
  rw [lift_inverse, Ring.inverse_eq_inv]
  change (f.val x.val)⁻¹ = 1 / f.val x.val
  simp [one_div]

theorem locus_open (f : Free n) : IsOpen {x : Fin n → ℝ | f.val x ≠ 0} :=
  isOpen_ne_fun (show ContDiff ℝ ∞ f.val from f.property).continuous continuous_const

abbrev dualCoordinates := @Applications.AD.SmoothDual.coordinates

def dualPoints (f : Free n) : Hom (Principal f) (DualNumber ℝ) ≃
    {p : (Fin n → ℝ) × (Fin n → ℝ) // f.val p.1 ≠ 0} :=
  (pointEquiv f).trans {
    toFun := fun z => ⟨dualCoordinates z.val,
      isUnit_iff_ne_zero.mp (TrivSqZeroExt.isUnit_iff_isUnit_fst.mp z.property)⟩
    invFun := fun p => ⟨dualCoordinates.symm p.val,
      TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr p.property)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem evaluate_dual (f : Free n) (x v : Fin n → ℝ) :
    (evaluate (fun i => (⟨x i,v i⟩ : DualNumber ℝ)) : Hom (Free n) (DualNumber ℝ)) f = (⟨f.val x, fderiv ℝ f.val x v⟩ : DualNumber ℝ) :=
  Applications.AD.SmoothAlgebras.dual_act f _

private def dualPair (a b : ℝ) : DualNumber ℝ := ⟨a, b⟩

theorem dual_inverse (f : Free n) (p : {p : (Fin n → ℝ) × (Fin n → ℝ) // f.val p.1 ≠ 0}) :
    (dualPoints f).symm p (inverse f) =
      (⟨1 / f.val p.val.1, -(fderiv ℝ f.val p.val.1 p.val.2) / (f.val p.val.1)^2⟩ : DualNumber ℝ) := by
  let a := f.val p.val.1
  let b := fderiv ℝ f.val p.val.1 p.val.2
  have ha : a ≠ 0 := p.property
  have hc : dualPair a b * dualPair (1/a) (-b/a^2) = 1 := by
    apply TrivSqZeroExt.ext
    · change a*(1/a)=1
      field_simp [ha]
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_one]
      simp only [dualPair, TrivSqZeroExt.fst, TrivSqZeroExt.snd, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      field_simp [ha]
      ring
  apply inverse_unique (B := DualNumber ℝ) (a := (⟨a, b⟩ : DualNumber ℝ)) _ hc
  have hu : IsUnit ((evaluate (fun i => (⟨p.val.1 i,p.val.2 i⟩ : DualNumber ℝ)) : Hom (Free n) (DualNumber ℝ)) f) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr ha)
  change dualPair a b * principalLift f (evaluate (fun i => (⟨p.val.1 i,p.val.2 i⟩ : DualNumber ℝ)) : Hom (Free n) (DualNumber ℝ)) hu (inverse f) = 1
  rw [lift_inverse]
  have hv : dualPair a b = (evaluate (fun i => (⟨p.val.1 i,p.val.2 i⟩ : DualNumber ℝ)) : Hom (Free n) (DualNumber ℝ)) f :=
    (evaluate_dual f p.val.1 p.val.2).symm
  rw [hv]
  exact Ring.mul_inverse_cancel _ hu

def residue : Hom (DualNumber ℝ) ℝ where
  toFun := TrivSqZeroExt.fst
  map_act _ _ := rfl

theorem points_residue (f : Free n) (h : Hom (Principal f) (DualNumber ℝ)) :
    (realPoints f (Hom.comp residue h)).val = (dualPoints f h).val.1 := rfl

def tangentScale (c : ℝ) : Hom (DualNumber ℝ) (DualNumber ℝ) :=
  Applications.AD.SmoothAlgebras.linear (c • LinearMap.id)

theorem points_tangentScale (f : Free n) (h : Hom (Principal f) (DualNumber ℝ)) (c : ℝ) :
    (dualPoints f (Hom.comp (tangentScale c) h)).val =
      ((dualPoints f h).val.1, fun i => c * (dualPoints f h).val.2 i) := by
  apply Prod.ext
  · funext i
    change (TrivSqZeroExt.map (c • LinearMap.id) (h (principalBase f (generator i)))).fst = _
    exact TrivSqZeroExt.fst_map _ _
  · funext i
    change (TrivSqZeroExt.map (c • LinearMap.id) (h (principalBase f (generator i)))).snd = _
    simp only [TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    rfl

end SquareKit.SmoothAlgebra.Localization
