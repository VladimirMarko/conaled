import SquareKit.SmoothManifoldOpenComparison
import SquareKit.SmoothManifoldLocalSmoothness

/-! The ordinary principal-open interpretation agrees with manifold maps. -/
noncomputable section
open CategoryTheory Set
open scoped Manifold ContDiff Topology
namespace SquareKit.ManifoldRealization
open EuclideanOpen SmoothAlgebra

/-- An ordinary smooth map of principal opens is smooth for the inherited
Mathlib manifold structures. Its ambient representative need only be smooth
on the source open. -/
theorem openMap_contMDiff {U V : Domain} (f : U ⟶ V) :
    ContMDiff (Model U.dimension) (Model V.dimension) ∞
      (show ordinaryOpen U → ordinaryOpen V from fun x => (show EuclideanOpen.Map U V from f) x) := by
  apply (ContMDiff.subtypeVal_comp_iff (ordinaryOpen V) _).mp
  intro x
  let g : EuclideanOpen.Map U V := f
  have h := g.smooth_representative.contDiffAt ((domain_open U).mem_nhds x.property)
  have hs := (contMDiffAt_subtype_iff (U := ordinaryOpen U)).mpr h.contMDiffAt
  exact hs.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y =>
    (g.representative_mem y).symm))


/-- The coordinate inclusion of an inherited principal-open chart. -/
def openChartInclusion (U : Domain) (i : ordinaryOpen U) :
    chartDomain (chartAt (Space U.dimension) i) ⟶ U :=
  domainInclusion _ _ (fun x hx => by
    change x ∈ Points (chartDomain (chartAt (Space U.dimension) i)) at hx
    rwa [chartDomain_locus, open_chart_target] at hx)

/-- Each inherited manifold chart is the ordinary coordinate inclusion. -/
theorem chart_principalIso (U : Domain) (i : ordinaryOpen U) :
    (openFamily U).charts.chart i ≫ (principalIso U).hom =
      embedding.map (openChartInclusion U i) := by
  have h : embedding.map (𝟙 (chartDomain (chartAt (Space U.dimension) i))) ≫
      (openFamily U).charts.chart i ≫ (toSingle U).realize =
      embedding.map (openChartInclusion U i) ≫ (singleAtlas U).toCharts.chart () :=
    (toSingle U).test i () (chartDomain (chartAt (Space U.dimension) i))
      (𝟙 _) (openChartInclusion U i) (fun x => by
      apply Subtype.ext
      exact open_chart_value U i x)
  rw [embedding.map_id, Category.id_comp] at h
  change _ ≫ ((toSingle U).realize ≫ (Charts.singleIso U).hom) = _
  rw [← Category.assoc, h, Category.assoc, Charts.single_chart, Category.comp_id]

/-- Transporting a principal-open map through the manifold comparison gives
the existing algebraic pullback interpretation. -/
theorem principalIso_naturality {U V : Domain} (f : U ⟶ V) :
    map (show ordinaryOpen U → ordinaryOpen V from fun x => (show EuclideanOpen.Map U V from f) x) (openMap_contMDiff f) ≫
      (principalIso V).hom = (principalIso U).hom ≫ embedding.map f := by
  let A := openFamily U
  let B := openFamily V
  let l := A.localMap B (show ordinaryOpen U → ordinaryOpen V from fun x => (show EuclideanOpen.Map U V from f) x)
    (openMap_contMDiff f)
  apply A.charts.hom_ext
  intro i
  apply cover_jointly_epic (A.charts.domain i) (l.defining i) (l.covers i) (embedding.obj V)
  intro k
  have ht := l.test i (l.index i k) _ (subInclusion _ _) (l.coordinate i k) (l.agreement i k)
  change embedding.map (subInclusion _ _) ≫ A.charts.chart i ≫ l.realize ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, Category.assoc
    (embedding.map (subInclusion _ _)) (A.charts.chart i) l.realize, ht, Category.assoc]
  rw [chart_principalIso]
  rw [← Category.assoc (A.charts.chart i) (principalIso U).hom (embedding.map f),
    chart_principalIso U i, ← embedding.map_comp, ← embedding.map_comp, ← embedding.map_comp]
  congr 1
  apply OpenFunctions.Map.ext
  intro x
  apply Subtype.ext
  have h := congrArg Subtype.val (l.agreement i k x)
  change ((show EuclideanOpen.Map _ _ from l.coordinate i k) x).val =
    ((show EuclideanOpen.Map U V from f) _).val
  rw [open_chart_value] at h
  have hy : A.charts.coordinate i ((subInclusion _ _).toFun x) =
      (openChartInclusion U i).toFun ((subInclusion _ _).toFun x) :=
    Subtype.ext (open_chart_value U i _)
  rw [hy] at h
  exact h.symm

/-- A Mathlib smooth map of these open submanifolds supplies the existing
ordinary smooth-map structure, with no ambient extension assumption. -/
def openMapOfContMDiff {U V : Domain} (f : ordinaryOpen U → ordinaryOpen V)
    (hf : ContMDiff (Model U.dimension) (Model V.dimension) ∞ f) : U ⟶ V where
  toFun := f
  smooth i := by
    intro x hx
    let q := OpenFunctions.extendZero (Points U) (fun y => (f y).val i)
    have hs := ((contDiff_apply ℝ (fun _ : Fin V.dimension => ℝ) i).contMDiff.comp
      (contMDiff_subtype_val (U := ordinaryOpen V))).comp hf
    have hq : ContMDiffAt (Model U.dimension) 𝓘(ℝ, ℝ) ∞
        (fun y : ordinaryOpen U => q y.val) ⟨x, hx⟩ :=
      (hs ⟨x, hx⟩).congr_of_eventuallyEq (Filter.Eventually.of_forall
        (fun y => OpenFunctions.extendZero_mem _ y))
    exact (contMDiffAt_subtype_iff.mp hq).contDiffAt.contDiffWithinAt

def openSmoothEquiv (U V : Domain) :
    (U ⟶ V) ≃ {f : ordinaryOpen U → ordinaryOpen V //
      ContMDiff (Model U.dimension) (Model V.dimension) ∞ f} where
  toFun f := ⟨(show EuclideanOpen.Map U V from f).toFun, openMap_contMDiff f⟩
  invFun f := openMapOfContMDiff f.val f.property
  left_inv _ := OpenFunctions.Map.ext (fun _ => rfl)
  right_inv _ := Subtype.ext rfl

private def principalArrowEquiv (U V : Domain) :
    (embedding.obj U ⟶ embedding.obj V) ≃
      (object U.dimension (ordinaryOpen U) ⟶ object V.dimension (ordinaryOpen V)) where
  toFun h := (principalIso U).hom ≫ h ≫ (principalIso V).inv
  invFun h := (principalIso U).inv ≫ h ≫ (principalIso V).hom
  left_inv h := by simp
  right_inv h := by simp

/-- Full correspondence for all arrows between the principal-open manifold
objects, transported from the existing ordinary-open embedding. -/
def principalHomEquiv (U V : Domain) :
    {f : ordinaryOpen U → ordinaryOpen V //
      ContMDiff (Model U.dimension) (Model V.dimension) ∞ f} ≃
        (object U.dimension (ordinaryOpen U) ⟶ object V.dimension (ordinaryOpen V)) :=
  (openSmoothEquiv U V).symm.trans
    ((EuclideanOpen.homEquiv U V).trans (principalArrowEquiv U V))

theorem principalHomEquiv_apply (U V : Domain)
    (f : {f : ordinaryOpen U → ordinaryOpen V //
      ContMDiff (Model U.dimension) (Model V.dimension) ∞ f}) :
    principalHomEquiv U V f = map f.val f.property := by
  apply (cancel_mono (principalIso V).hom).mp
  change ((principalIso U).hom ≫ embedding.map (openMapOfContMDiff f.val f.property) ≫
    (principalIso V).inv) ≫ (principalIso V).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (principalIso_naturality (openMapOfContMDiff f.val f.property)).symm

theorem principal_inverse_forward (U V : Domain)
    (f : ordinaryOpen U → ordinaryOpen V)
    (hf : ContMDiff (Model U.dimension) (Model V.dimension) ∞ f) :
    (principalHomEquiv U V).symm (map f hf) = ⟨f, hf⟩ := by
  rw [← principalHomEquiv_apply U V ⟨f, hf⟩]
  exact (principalHomEquiv U V).symm_apply_apply _

theorem principal_forward_inverse (U V : Domain)
    (h : object U.dimension (ordinaryOpen U) ⟶ object V.dimension (ordinaryOpen V)) :
    map ((principalHomEquiv U V).symm h).val ((principalHomEquiv U V).symm h).property = h := by
  rw [← principalHomEquiv_apply]
  exact (principalHomEquiv U V).apply_symm_apply h

end SquareKit.ManifoldRealization
