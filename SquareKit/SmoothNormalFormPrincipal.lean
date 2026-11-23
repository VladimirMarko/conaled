import SquareKit.SmoothTransversePullback
import SquareKit.SmoothManifoldPrincipalMaps
import SquareKit.SmoothOpenCoordinatePullbacks

/-! Principal-domain maps for the actual finite-coordinate regular-level chart. -/
noncomputable section
open CategoryTheory Set
open scoped ContDiff Manifold

namespace SquareKit.SmoothNormalFormPrincipal
open ManifoldRealization EuclideanOpen SmoothAlgebra

/-- Split a finite tuple into its first and last coordinate blocks. -/
def split (m n : ℕ) : Space (m + n) ≃L[ℝ] (Space m × Space n) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun x => (fun i => x (Fin.castAdd n i), fun i => x (Fin.natAdd m i))
    invFun := fun x => Fin.addCases x.1 x.2
    left_inv := by
      intro x
      funext i
      exact Fin.addCases (fun j => by simp) (fun j => by simp) i
    right_inv := by intro x; ext i <;> simp
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

@[simp] theorem split_first (m n : ℕ) (x : Space (m+n)) (i : Fin m) :
    (split m n x).1 i = x (Fin.castAdd n i) := rfl

@[simp] theorem split_last (m n : ℕ) (x : Space (m+n)) (i : Fin n) :
    (split m n x).2 i = x (Fin.natAdd m i) := rfl

@[simp] theorem split_symm (m n : ℕ) (x : Space m × Space n) :
    (split m n).symm x = Fin.addCases x.1 x.2 := rfl

@[simp] theorem split_addCases (m n : ℕ) (x : Space m) (y : Space n) :
    split m n (Fin.addCases x y) = (x, y) := (split m n).apply_symm_apply (x, y)

abbrev sourceDomain {a b : ℕ} (e : OpenPartialHomeomorph (Space a) (Space b)) : Domain :=
  ⟨a, openDefining e.source e.open_source⟩

abbrev targetDomain {a b : ℕ} (e : OpenPartialHomeomorph (Space a) (Space b)) : Domain :=
  ⟨b, openDefining e.target e.open_target⟩

theorem sourceDomain_points {a b : ℕ} (e : OpenPartialHomeomorph (Space a) (Space b)) :
    Points (sourceDomain e) = e.source := openDefining_locus e.source e.open_source

theorem targetDomain_points {a b : ℕ} (e : OpenPartialHomeomorph (Space a) (Space b)) :
    Points (targetDomain e) = e.target := openDefining_locus e.target e.open_target

def forwardMap {a b : ℕ} (e : OpenPartialHomeomorph (Space a) (Space b))
    (he : ContDiffOn ℝ ∞ e e.source) : sourceDomain e ⟶ targetDomain e where
  toFun x := ⟨e x.val, by
    change e x.val ∈ Points (targetDomain e)
    rw [targetDomain_points]
    exact e.map_source ((sourceDomain_points e) ▸ x.property)⟩
  smooth i := (OpenFunctions.representative_iff _ (fun x => e x i) (fun _ => rfl)).mpr
    (by
      change ContDiffOn ℝ ∞ (fun x => e x i) (Points (sourceDomain e))
      rw [sourceDomain_points]
      exact (contDiff_apply ℝ (fun _ : Fin b => ℝ) i).comp_contDiffOn he)

/-- Both principal maps are constructed from smoothness on their actual open domains. -/
def principalIso {a b : ℕ} (e : OpenPartialHomeomorph (Space a) (Space b))
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) :
    sourceDomain e ≅ targetDomain e where
  hom := forwardMap e he
  inv := forwardMap e.symm hi
  hom_inv_id := OpenFunctions.Map.ext (fun x => Subtype.ext
    (e.left_inv ((sourceDomain_points e) ▸ x.property)))
  inv_hom_id := OpenFunctions.Map.ext (fun x => Subtype.ext
    (e.right_inv ((targetDomain_points e) ▸ x.property)))

/-- Restricting the full domain has the same points as the specified principal domain. -/
def fullSubdomainIso (U : Domain) : subdomain (full U.dimension) U.defining ≅ U where
  hom := domainInclusion _ _ (fun _ h => right_ne_zero_of_mul h)
  inv := domainInclusion _ _ (fun _ h => mul_ne_zero one_ne_zero h)
  hom_inv_id := OpenFunctions.Map.ext (fun _ => rfl)
  inv_hom_id := OpenFunctions.Map.ext (fun _ => rfl)

end SquareKit.SmoothNormalFormPrincipal

namespace SquareKit.SmoothTransversePullback.LocalModel
open ManifoldRealization SmoothTransversality SmoothNormalFormPrincipal EuclideanOpen SmoothAlgebra
variable {m n p : ℕ} {M N P : Type}
  [TopologicalSpace M] [ChartedSpace (Space m) M]
  [TopologicalSpace N] [ChartedSpace (Space n) N]
  [TopologicalSpace P] [ChartedSpace (Space p) P]
  {f : M → P} {g : N → P} {q : Pullback f g}
  (A : LocalModel (m := m) (n := n) (p := p) q)

/-- Kernel coordinates precede the difference coordinates, matching `insertZero`. -/
def targetCoordinates : (Space p × (derivative (m := m) (n := n) (p := p) q).ker)
    ≃L[ℝ] Space ((m+n-p)+p) :=
  ((ContinuousLinearEquiv.prodComm ℝ _ _).trans
    (A.coordinates.prodCongr (ContinuousLinearEquiv.refl ℝ (Space p)))).trans
    (split (m+n-p) p).symm

def finiteChart : OpenPartialHomeomorph (Space (m+n)) (Space ((m+n-p)+p)) :=
  ((split m n).toHomeomorph.toOpenPartialHomeomorph.trans A.normal.chart).trans
    A.targetCoordinates.toHomeomorph.toOpenPartialHomeomorph

theorem finiteChart_source : A.finiteChart.source = (split m n) ⁻¹' A.normal.chart.source := by
  ext x
  simp [finiteChart]

theorem finiteChart_target : A.finiteChart.target =
    A.targetCoordinates.symm ⁻¹' A.normal.chart.target := by
  ext x
  simp [finiteChart]

theorem finiteChart_smooth : ContDiffOn ℝ ∞ A.finiteChart A.finiteChart.source := by
  rw [A.finiteChart_source]
  exact A.targetCoordinates.contDiff.comp_contDiffOn
    (A.normal.smooth.comp (split m n).contDiff.contDiffOn (fun _ h => h))

theorem finiteChart_symm_smooth : ContDiffOn ℝ ∞ A.finiteChart.symm A.finiteChart.target := by
  rw [A.finiteChart_target]
  exact (split m n).symm.contDiff.comp_contDiffOn
    (A.normal.smooth_symm.comp A.targetCoordinates.symm.contDiff.contDiffOn (fun _ h => h))

def normalPrincipalIso : sourceDomain A.finiteChart ≅ targetDomain A.finiteChart :=
  SmoothNormalFormPrincipal.principalIso A.finiteChart A.finiteChart_smooth A.finiteChart_symm_smooth

theorem targetCoordinates_symm_apply (v : Space ((m+n-p)+p)) :
    A.targetCoordinates.symm v =
      ((split (m+n-p) p v).2, A.coordinates.symm (split (m+n-p) p v).1) := rfl

theorem finiteChart_apply (x : Space (m+n)) :
    A.finiteChart x = Fin.addCases
      (A.coordinates (A.normal.projection (split m n x - coordinateCenter q.val.1 q.val.2)))
      (coordinateDifference (m := m) (n := n) (p := p) f g q.val.1 q.val.2 (split m n x)) := by
  change A.targetCoordinates (A.normal.chart (split m n x)) = _
  rw [A.normal.chart_apply]
  rfl

theorem finiteChart_last (x : Space (m+n)) :
    (split (m+n-p) p (A.finiteChart x)).2 =
      coordinateDifference (m := m) (n := n) (p := p) f g q.val.1 q.val.2 (split m n x) := by
  rw [A.finiteChart_apply]
  funext i
  simp

theorem finiteChart_symm_insertZero (v : Space (m+n-p)) :
    A.finiteChart.symm (Fin.addCases v (fun _ : Fin p => 0)) =
      (split m n).symm (A.parameterize v) := by
  change (split m n).symm (A.normal.chart.symm
    (A.targetCoordinates.symm (Fin.addCases v (fun _ : Fin p => 0)))) = _
  rw [A.targetCoordinates_symm_apply]
  simp only [split_addCases]
  change (split m n).symm (A.normal.chart.symm (0, A.coordinates.symm v)) = _
  unfold parameterize SmoothRegularLevel.NormalForm.parameterize
  rw [coordinateDifference_center q.property]

theorem finiteChart_insertZero_mem (v : Space (m+n-p)) :
    Fin.addCases v (fun _ : Fin p => 0) ∈ A.finiteChart.target ↔ v ∈ A.target := by
  rw [A.finiteChart_target]
  change A.targetCoordinates.symm (Fin.addCases v (fun _ : Fin p => 0)) ∈
    A.normal.chart.target ↔ _
  rw [A.targetCoordinates_symm_apply]
  simp only [split_addCases]
  change (0, A.coordinates.symm v) ∈ A.normal.chart.target ↔
    (coordinateDifference (m := m) (n := n) (p := p) f g q.val.1 q.val.2
      (coordinateCenter q.val.1 q.val.2), A.coordinates.symm v) ∈ A.normal.chart.target
  rw [coordinateDifference_center q.property]

abbrev zeroDomain := subdomain (full (m+n-p))
  (inverseDefining (Coordinates.insertZero (m+n-p) p) (targetDomain A.finiteChart).defining)

theorem zeroDomain_points : Points A.zeroDomain = A.target := by
  ext v
  change (1 * (inverseDefining (Coordinates.insertZero (m+n-p) p)
    (targetDomain A.finiteChart).defining).val v ≠ 0) ↔ _
  rw [one_mul, Coordinates.restricted_points (m+n-p) p _ ⟨v, one_ne_zero⟩]
  change Fin.addCases v (fun _ => 0) ∈ Points (targetDomain A.finiteChart) ↔ _
  rw [targetDomain_points, A.finiteChart_insertZero_mem]

/-- The zero-coordinate inverse domain is the ordinary regular-level chart domain. -/
def levelPrincipalIso : chartDomain A.chart ≅ A.zeroDomain where
  hom := domainInclusion _ _ (by
    intro x hx
    change x ∈ Points A.zeroDomain
    rw [A.zeroDomain_points]
    change x ∈ A.chart.target
    exact (chartDomain_locus A.chart) ▸ hx)
  inv := domainInclusion _ _ (by
    intro x hx
    change x ∈ Points (chartDomain A.chart)
    rw [chartDomain_locus]
    change x ∈ A.target
    exact (A.zeroDomain_points) ▸ hx)
  hom_inv_id := OpenFunctions.Map.ext (fun _ => rfl)
  inv_hom_id := OpenFunctions.Map.ext (fun _ => rfl)

def normalParameterMap : chartDomain A.chart ⟶ sourceDomain A.finiteChart :=
  A.levelPrincipalIso.hom ≫
    inverseRestriction (Coordinates.insertZero (m+n-p) p) (targetDomain A.finiteChart).defining ≫
    (fullSubdomainIso (targetDomain A.finiteChart)).hom ≫ A.normalPrincipalIso.inv

theorem normalParameterMap_apply (v : Points (chartDomain A.chart)) :
    ((show EuclideanOpen.Map _ _ from A.normalParameterMap) v).val =
      (split m n).symm (A.parameterize v.val) := by
  change A.finiteChart.symm
    ((Coordinates.insertZero (m+n-p) p).toFun ⟨v.val, one_ne_zero⟩).val = _
  have hi : ((Coordinates.insertZero (m+n-p) p).toFun ⟨v.val, one_ne_zero⟩).val =
      Fin.addCases v.val (fun _ : Fin p => 0) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · change (Fin.addCases (motive := fun _ => Operation (m+n-p)) projection
        (fun _ => constant (m+n-p) 0) (Fin.castAdd p j)).val v.val = _
      simp [projection]
    · change (Fin.addCases (motive := fun _ => Operation (m+n-p)) projection
        (fun _ => constant (m+n-p) 0) (Fin.natAdd (m+n-p) j)).val v.val = _
      simp [constant]
  rw [hi, A.finiteChart_symm_insertZero]

/-- The actual coordinate difference, expressed in the finite normal chart. -/
def normalDifferenceMap : sourceDomain A.finiteChart ⟶ full p :=
  A.normalPrincipalIso.hom ≫ (fullSubdomainIso (targetDomain A.finiteChart)).inv ≫
    subInclusion (full ((m+n-p)+p)) (targetDomain A.finiteChart).defining ≫
    Coordinates.last (m+n-p) p

def levelToPoint : chartDomain A.chart ⟶ full 0 :=
  A.levelPrincipalIso.hom ≫ subInclusion (full (m+n-p))
    (inverseDefining (Coordinates.insertZero (m+n-p) p)
      (targetDomain A.finiteChart).defining) ≫ Coordinates.toPoint (m+n-p)

theorem normalDifferenceMap_apply (v : Points (sourceDomain A.finiteChart)) :
    ((show EuclideanOpen.Map _ _ from A.normalDifferenceMap) v).val =
      coordinateDifference (m := m) (n := n) (p := p) f g q.val.1 q.val.2
        (split m n v.val) := by
  exact A.finiteChart_last v.val

/-- The regular-level chart satisfies the coordinate pullback universal property
at every sheaf stage, including stages with nilpotents. -/
theorem normal_isPullback : CategoryTheory.IsPullback
    (embedding.map A.normalParameterMap) (embedding.map A.levelToPoint)
    (embedding.map A.normalDifferenceMap) (embedding.map (Coordinates.zero p)) := by
  apply (Coordinates.restricted_zeroFiber_isPullback (m+n-p) p
    (targetDomain A.finiteChart).defining).of_iso'
      (embedding.mapIso A.levelPrincipalIso)
      (embedding.mapIso (A.normalPrincipalIso.trans
        (fullSubdomainIso (targetDomain A.finiteChart)).symm))
      (Iso.refl _) (Iso.refl _)
  · simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
      normalParameterMap]
    simp only [← embedding.map_comp]
    congr 1
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
  · simp only [Functor.mapIso_hom, levelToPoint, embedding.map_comp,
      Iso.refl_hom, Category.comp_id]
  · simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
      normalDifferenceMap, embedding.map_comp, Iso.refl_hom, Category.comp_id,
      Category.assoc]
  · simp

end SquareKit.SmoothTransversePullback.LocalModel
