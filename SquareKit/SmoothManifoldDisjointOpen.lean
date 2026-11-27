import SquareKit.SmoothManifoldAction
import SquareKit.SheafCoproductGeometry

/-! Realization of disjoint open covers, with the canonical inclusion maps. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Set IsManifold
open scoped Manifold ContDiff
namespace SquareKit.ManifoldRealization
open EuclideanOpen SmoothManifoldAction

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
  [IsManifold (modelWithCorners n) ∞ M]

omit [IsManifold (modelWithCorners n) ∞ M] in
/-- The inverse of a smooth chart is smooth on its actual open domain. -/
theorem chartPoint_smooth (e : OpenPartialHomeomorph M (Space n))
    (he : e ∈ IsManifold.maximalAtlas (modelWithCorners n) ∞ M) :
    ContMDiff (modelWithCorners n) (modelWithCorners n) ∞
      (show ordinaryOpen (chartDomain e) → M from chartPoint e) := by
  intro x
  change ContMDiffAt (modelWithCorners n) (modelWithCorners n) ∞
    (fun x : ordinaryOpen (chartDomain e) => e.symm x.val) x
  apply (contMDiffAt_subtype_iff (U := ordinaryOpen (chartDomain e))).mpr
  exact contMDiffAt_symm_of_mem_maximalAtlas he ((chartDomain_locus e) ▸ x.property)

/-- A chart inclusion is the interpretation of its actual inverse coordinate map. -/
theorem chart_eq_hat (A : ChartFamily n M) (i : A.Index) :
    A.charts.chart i ≫ (atlasIso A).inv =
      hat (chartPoint (A.chart i)) (chartPoint_smooth _ (A.smooth i)) := by
  apply SmoothManifoldAction.hom_ext
  intro x
  apply pointEquiv.injective
  rw [hat_eval]
  have h := A.charts.realMap_chart (ChartFamily.preferred (n := n) (M := M)).charts
    A.atlas.covers (ChartFamily.preferred (n := n) (M := M)).atlas.covers
    (atlasIso A).inv i x
  have hid : A.charts.realMap (ChartFamily.preferred (n := n) (M := M)).charts
      A.atlas.covers (ChartFamily.preferred (n := n) (M := M)).atlas.covers
      (atlasIso A).inv = id :=
    A.charts.realMap_realize _ _ _ (A.localMap .preferred id contMDiff_id)
  rw [hid] at h
  exact h.symm

/-- Interpretation commutes with precomposition by an admitted principal map. -/
theorem hat_precomp {W V : Domain} (f : ordinaryOpen V → M)
    (hf : ContMDiff (modelWithCorners V.dimension) (modelWithCorners n) ∞ f)
    (r : W ⟶ V) : embedding.map r ≫ hat f hf =
      hat (f ∘ r.toFun) (hf.comp (euclideanOpenMap_contMDiff r)) := by
  apply (cancel_epi (principalIso W).hom).mp
  simp only [hat, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← principalIso_naturality]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← map_comp]

/-- Interpretation commutes with postcomposition by an actual smooth map. -/
theorem hat_postcomp {m : ℕ} {N : Type} [TopologicalSpace N]
    [ChartedSpace (Space m) N] [IsManifold (modelWithCorners m) ∞ N]
    {W : Domain} (f : ordinaryOpen W → M)
    (hf : ContMDiff (modelWithCorners W.dimension) (modelWithCorners n) ∞ f)
    (g : M → N) (hg : ContMDiff (modelWithCorners n) (modelWithCorners m) ∞ g) :
    hat f hf ≫ map g hg = hat (g ∘ f) (hg.comp hf) := by
  simp only [hat, Category.assoc, ← map_comp]

namespace DisjointOpen
variable {J : Type} (U : J → TopologicalSpace.Opens M)

def inclusion (i : J) : object n (U i) ⟶ object n M :=
  map (Subtype.val : U i → M) contMDiff_subtype_val

/-- The canonical assembly of the interpreted open inclusions. -/
def assembly : SheafCoproductLocal.total (fun i => object n (U i)) ⟶ object n M :=
  SheafCoproductLocal.desc _ (inclusion U)

@[reassoc (attr := simp)] theorem inclusion_assembly (i : J) :
    SheafCoproductLocal.inclusion (fun i => object n (U i)) i ≫ assembly U = inclusion U i :=
  SheafCoproductLocal.inclusion_desc _ _ _

variable (cover : ∀ x : M, ∃ i, x ∈ U i)

/-- Restrict ordinary charts to the chosen open pieces. -/
def subordinate : ChartFamily n M where
  Index := J × M
  chart p := (chartAt (Space n) p.2).restr (U p.1)
  smooth p := restr_mem_maximalAtlas _ (chart_mem_maximalAtlas p.2) (U p.1).isOpen
  covers x := by
    obtain ⟨i, hi⟩ := cover x
    refine ⟨(i,x), ?_⟩
    change x ∈ (chartAt (Space n) x).source ∧ x ∈ interior (U i : Set M)
    rw [(U i).isOpen.interior_eq]
    exact ⟨mem_chart_source (Space n) x, hi⟩

def chartLift (p : (subordinate (n := n) U cover).Index) :
    ordinaryOpen ((subordinate (n := n) U cover).charts.domain p) → U p.1 :=
  fun x => ⟨chartPoint ((subordinate (n := n) U cover).chart p) x,
    interior_subset (chartPoint_source ((subordinate (n := n) U cover).chart p) x).2⟩

theorem chartLift_smooth (p : (subordinate (n := n) U cover).Index) :
    ContMDiff (modelWithCorners n) (modelWithCorners n) ∞ (chartLift U cover p) := by
  apply (ContMDiff.subtypeVal_comp_iff (U p.1) _).mp
  exact chartPoint_smooth _ ((subordinate (n := n) U cover).smooth p)

variable (disjoint : ∀ i j, i ≠ j → Disjoint (U i : Set M) (U j : Set M))
variable {F : Sheaf SmoothOpenSite.topology Type} (k : ∀ i, object n (U i) ⟶ F)
include disjoint

theorem lifted_test {W : Domain} (p q : (subordinate (n := n) U cover).Index)
    (a : W ⟶ (subordinate (n := n) U cover).charts.domain p)
    (b : W ⟶ (subordinate (n := n) U cover).charts.domain q)
    (h : ∀ x, (subordinate (n := n) U cover).charts.coordinate p (a.toFun x) =
      (subordinate (n := n) U cover).charts.coordinate q (b.toFun x)) :
    embedding.map a ≫ hat (chartLift U cover p) (chartLift_smooth U cover p) ≫ k p.1 =
      embedding.map b ≫ hat (chartLift U cover q) (chartLift_smooth U cover q) ≫ k q.1 := by
  classical
  by_cases hi : p.1 = q.1
  · rcases p with ⟨i, p⟩
    rcases q with ⟨j, q⟩
    dsimp at hi
    subst j
    rw [← Category.assoc, ← Category.assoc, hat_precomp, hat_precomp]
    have he : chartLift U cover (i,p) ∘ a.toFun = chartLift U cover (i,q) ∘ b.toFun := by
      funext x
      exact Subtype.ext (h x)
    simp only [he]
  · apply empty_domain_hom_ext W
    refine ⟨fun x => Set.disjoint_left.mp (disjoint _ _ hi)
      (chartLift U cover p (a.toFun x)).property ?_⟩
    change (subordinate (n := n) U cover).charts.coordinate p (a.toFun x) ∈ U q.1
    rw [h x]
    exact (chartLift U cover q (b.toFun x)).property

/-- Glue arbitrary sheaf maps from the disjoint open pieces using actual charts. -/
def descend : object n M ⟶ F :=
  (atlasIso (subordinate (n := n) U cover)).hom ≫
    (subordinate (n := n) U cover).charts.descend
      (fun p => hat (chartLift U cover p) (chartLift_smooth U cover p) ≫ k p.1)
      (fun r => lifted_test U cover disjoint k r.first r.second r.left r.right r.agreement)

theorem chart_descend (p : (subordinate (n := n) U cover).Index) :
    (subordinate (n := n) U cover).charts.chart p ≫ (atlasIso (subordinate (n := n) U cover)).inv ≫
      descend U cover disjoint k =
      hat (chartLift U cover p) (chartLift_smooth U cover p) ≫ k p.1 := by
  simp only [descend, Iso.inv_hom_id_assoc]
  exact Charts.chart_descend (subordinate (n := n) U cover).charts
    (fun p => hat (chartLift U cover p) (chartLift_smooth U cover p) ≫ k p.1)
    (fun r => lifted_test U cover disjoint k r.first r.second r.left r.right r.agreement) p

theorem component_test {W : Domain} (i : J) (f : ordinaryOpen W → U i)
    (hf : ContMDiff (modelWithCorners W.dimension) (modelWithCorners n) ∞ f)
    (q : (subordinate (n := n) U cover).Index) (b : W ⟶ (subordinate (n := n) U cover).charts.domain q)
    (h : ∀ x, (f x).val = (subordinate (n := n) U cover).charts.coordinate q (b.toFun x)) :
    hat f hf ≫ k i =
      embedding.map b ≫ hat (chartLift U cover q) (chartLift_smooth U cover q) ≫ k q.1 := by
  classical
  by_cases hi : i = q.1
  · rcases q with ⟨j, q⟩
    dsimp at hi
    subst j
    rw [← Category.assoc, hat_precomp]
    have he : f = chartLift U cover (i,q) ∘ b.toFun := funext (fun x => Subtype.ext (h x))
    simp only [he]
  · apply empty_domain_hom_ext W
    refine ⟨fun x => Set.disjoint_left.mp (disjoint _ _ hi) (f x).property ?_⟩
    exact (h x).symm ▸ (chartLift U cover q (b.toFun x)).property

/-- The descended map recovers each supplied map on the whole open piece. -/
@[reassoc] theorem inclusion_descend (i : J) :
    inclusion U i ≫ descend U cover disjoint k = k i := by
  let A := subordinate (n := n) U cover
  let B := ChartFamily.preferred (n := n) (M := U i)
  let l := B.localMap A (Subtype.val : U i → M) contMDiff_subtype_val
  have hl : inclusion U i ≫ (atlasIso A).hom = l.realize := by
    change B.interpret .preferred Subtype.val contMDiff_subtype_val ≫
      (ChartFamily.preferred (n := n) (M := M)).interpret A id contMDiff_id = _
    rw [← ChartFamily.interpret_comp]
    rfl
  apply B.charts.hom_ext
  intro p
  apply cover_jointly_epic (B.charts.domain p) (l.defining p) (l.covers p) F
  intro q
  change embedding.map (subInclusion _ _) ≫ B.charts.chart p ≫
    (inclusion U i ≫ ((atlasIso A).hom ≫ _)) = _
  rw [← Category.assoc (inclusion U i), hl]
  rw [← Category.assoc (B.charts.chart p),
    ← Category.assoc (embedding.map (subInclusion _ _))]
  rw [l.test p (l.index p q) _ (subInclusion _ _) (l.coordinate p q) (l.agreement p q)]
  rw [Category.assoc]
  rw [Charts.chart_descend (subordinate (n := n) U cover).charts
    (fun p => hat (chartLift U cover p) (chartLift_smooth U cover p) ≫ k p.1)
    (fun r => lifted_test U cover disjoint k r.first r.second r.left r.right r.agreement)
    (l.index p q)]
  have hb : B.charts.chart p = hat (chartPoint (B.chart p)) (chartPoint_smooth _ (B.smooth p)) := by
    have h := chart_eq_hat B p
    simpa only [B, atlasIso, ChartFamily.comparison_refl, Iso.refl_inv, Category.comp_id] using h
  rw [hb]
  simpa only [← Category.assoc, hat_precomp] using
    (component_test U cover disjoint k i _
      ((chartPoint_smooth _ (B.smooth p)).comp (euclideanOpenMap_contMDiff (subInclusion _ _)))
      (l.index p q) (l.coordinate p q) (l.agreement p q)).symm

include cover in
omit disjoint in
/-- Maps out of the manifold realization are determined on the open cover. -/
theorem hom_ext (f g : object n M ⟶ F)
    (h : ∀ i, inclusion U i ≫ f = inclusion U i ≫ g) : f = g := by
  apply (cancel_epi (atlasIso (subordinate (n := n) U cover)).inv).mp
  apply (subordinate (n := n) U cover).charts.hom_ext
  intro p
  rw [← Category.assoc, ← Category.assoc, chart_eq_hat]
  change hat (Subtype.val ∘ chartLift U cover p)
    (contMDiff_subtype_val.comp (chartLift_smooth U cover p)) ≫ f =
    hat (Subtype.val ∘ chartLift U cover p)
      (contMDiff_subtype_val.comp (chartLift_smooth U cover p)) ≫ g
  rw [← hat_postcomp (chartLift U cover p) (chartLift_smooth U cover p)
    (Subtype.val : U p.1 → M) contMDiff_subtype_val, Category.assoc, Category.assoc]
  exact congrArg (fun z => hat (chartLift U cover p) (chartLift_smooth U cover p) ≫ z) (h p.1)

/-- The canonical coproduct assembly is an isomorphism, with charts proving both laws. -/
def assemblyIso : SheafCoproductLocal.total (fun i => object n (U i)) ≅ object n M where
  hom := assembly U
  inv := descend U cover disjoint (SheafCoproductLocal.inclusion _)
  hom_inv_id := by
    apply colimit.hom_ext
    intro i
    change SheafCoproductLocal.inclusion (fun i => object n (U i)) i.as ≫
      (assembly U ≫ descend U cover disjoint (SheafCoproductLocal.inclusion _)) =
      SheafCoproductLocal.inclusion (fun i => object n (U i)) i.as ≫ 𝟙 _
    simp only [← Category.assoc, inclusion_assembly, inclusion_descend, Category.comp_id]
  inv_hom_id := by
    apply hom_ext U cover
    intro i
    simp only [← Category.assoc, inclusion_descend, inclusion_assembly, Category.comp_id]

@[simp] theorem assemblyIso_hom : (assemblyIso (n := n) U cover disjoint).hom = assembly U := rfl

end DisjointOpen
end SquareKit.ManifoldRealization
