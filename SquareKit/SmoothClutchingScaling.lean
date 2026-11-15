import SquareKit.SmoothCechRefinement
import SquareKit.SmoothClutchingAtlas

/-! Actual nonidentity base maps of the doubled-origin sheaf. -/
noncomputable section
open scoped ContDiff
namespace SquareKit.SmoothClutching
open CategoryTheory CategoryTheory.Limits Opposite EuclideanOpen SmoothOpenSite SmoothAlgebra

def lineScale (r : ℝ) : line ⟶ line where
  toFun x := ⟨fun i => r * x.val i, by simp [line, full, Localization.locus]⟩
  smooth i := (OpenFunctions.representative_iff _ (fun x => r * x i) (fun _ => rfl)).mpr
    (contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) i)).contDiffOn

def puncturedScale (r : ℝ) (hr : r ≠ 0) : punctured ⟶ punctured where
  toFun x := ⟨fun i => r * x.val i, by
    have hx : x.val 0 ≠ 0 := by
      have h := x.property
      change (1 : ℝ) * x.val 0 ≠ 0 at h
      simpa only [one_mul] using h
    change (1 : ℝ) * (r * x.val 0) ≠ 0
    simpa only [one_mul] using mul_ne_zero hr hx⟩
  smooth i := (OpenFunctions.representative_iff _ (fun x => r * x i) (fun _ => rfl)).mpr
    (contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) i)).contDiffOn

theorem scale_inclusion (r : ℝ) (hr : r ≠ 0) :
    puncturedScale r hr ≫ subInclusion line (generator 0) =
      subInclusion line (generator 0) ≫ lineScale r := OpenFunctions.Map.ext (fun _ => rfl)

def baseScale (r : ℝ) (hr : r ≠ 0) : base ⟶ base :=
  pushout.desc (embedding.map (lineScale r) ≫ left) (embedding.map (lineScale r) ≫ right) (by
    have h : inclusion ≫ embedding.map (lineScale r) = embedding.map (puncturedScale r hr) ≫ inclusion := by
      change embedding.map _ ≫ embedding.map _ = embedding.map _ ≫ embedding.map _
      rw [← Functor.map_comp, ← Functor.map_comp, scale_inclusion]
    rw [← Category.assoc, h, Category.assoc, overlap.w, ← Category.assoc, ← h, Category.assoc])

@[simp, reassoc] theorem left_baseScale (r : ℝ) (hr : r ≠ 0) :
    left ≫ baseScale r hr = embedding.map (lineScale r) ≫ left := pushout.inl_desc _ _ _

@[simp, reassoc] theorem right_baseScale (r : ℝ) (hr : r ≠ 0) :
    right ≫ baseScale r hr = embedding.map (lineScale r) ≫ right := pushout.inr_desc _ _ _

theorem lineScale_comp (r s : ℝ) : lineScale r ≫ lineScale s = lineScale (s*r) := by
  apply OpenFunctions.Map.ext
  intro x
  apply Subtype.ext
  funext i
  exact (mul_assoc s r (x.val i)).symm

theorem baseScale_comp (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) :
    baseScale r hr ≫ baseScale s hs = baseScale (s*r) (mul_ne_zero hs hr) := by
  apply pushout.hom_ext
  · change left ≫ _ = left ≫ _
    rw [← Category.assoc, left_baseScale, Category.assoc, left_baseScale, left_baseScale, ← Category.assoc, ← Functor.map_comp, lineScale_comp]
  · change right ≫ _ = right ≫ _
    rw [← Category.assoc, right_baseScale, Category.assoc, right_baseScale, right_baseScale, ← Category.assoc, ← Functor.map_comp, lineScale_comp]

def scalingAtlasMap (r : ℝ) (hr : r ≠ 0) :
    SmoothRepresentedCover.AtlasMap Represented.atlas Represented.atlas (baseScale r hr) where
  index := id
  chart _ := lineScale r
  commutes i := by cases i <;> exact (by first | exact (left_baseScale r hr).symm | exact (right_baseScale r hr).symm)

theorem scaling_two_three : baseScale 2 (by norm_num) ≫ baseScale 3 (by norm_num) =
    baseScale 6 (by norm_num) := by
  have h := baseScale_comp 2 3 (by norm_num) (by norm_num)
  norm_num at h
  exact h

theorem lineScale_one : lineScale 1 = 𝟙 line := by
  apply OpenFunctions.Map.ext
  intro x
  apply Subtype.ext
  funext i
  exact one_mul (x.val i)

def lineScalingIso (r : ℝ) (hr : r ≠ 0) : line ≅ line where
  hom := lineScale r
  inv := lineScale r⁻¹
  hom_inv_id := by rw [lineScale_comp, inv_mul_cancel₀ hr, lineScale_one]
  inv_hom_id := by rw [lineScale_comp, mul_inv_cancel₀ hr, lineScale_one]

theorem baseScale_one : baseScale 1 one_ne_zero = 𝟙 base := by
  apply pushout.hom_ext
  · change left ≫ _ = left ≫ _
    rw [left_baseScale, lineScale_one, embedding.map_id]
    simp
  · change right ≫ _ = right ≫ _
    rw [right_baseScale, lineScale_one, embedding.map_id]
    simp

def baseScalingIso (r : ℝ) (hr : r ≠ 0) : base ≅ base where
  hom := baseScale r hr
  inv := baseScale r⁻¹ (inv_ne_zero hr)
  hom_inv_id := by rw [baseScale_comp]; simpa only [inv_mul_cancel₀ hr] using baseScale_one
  inv_hom_id := by rw [baseScale_comp]; simpa only [mul_inv_cancel₀ hr] using baseScale_one

theorem baseScale_ne_identity (r : ℝ) (hr : r ≠ 0) (hne : r ≠ 1) : baseScale r hr ≠ 𝟙 base := by
  intro h
  have he := left_baseScale r hr
  rw [h, Category.comp_id] at he
  have hm : embedding.map (lineScale r) = 𝟙 lineSheaf := by
    apply (cancel_mono left).mp
    simpa only [Category.id_comp] using he.symm
  have hl : lineScale r = 𝟙 line := by
    apply (homEquiv _ _).injective
    change embedding.map _ = embedding.map _
    simpa only [embedding.map_id] using hm
  have hh := congrArg (fun u : line ⟶ line =>
    ((show EuclideanOpen.Map _ _ from u) (realLinePoint 1)).val 0) hl
  apply hne
  change r * 1 = 1 at hh
  simpa only [mul_one] using hh

end SquareKit.SmoothClutching
