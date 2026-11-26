import SquareKit.SmoothCechGauge
import SquareKit.SheafCoverCechMaps

/-! Represented atlas refinements and their selected quotient comparisons. -/
noncomputable section
namespace SquareKit.SmoothRepresentedCover
open CategoryTheory CategoryTheory.Limits Opposite EuclideanOpen SmoothOpenSite
variable {X Y Z : Sheaf topology Type} {I J K : Type}

/-- Both atlases carry their actual covering and pullback evidence. No existence
of arbitrary represented refinements is asserted. -/
structure AtlasMap (A : Atlas X I) (B : Atlas Y J) (f : Y ⟶ X) where
  index : J → I
  chart : ∀ j, B.domain j ⟶ A.domain (index j)
  commutes : ∀ j, embedding.map (chart j) ≫ A.chart (index j) = B.chart j ≫ f

namespace AtlasMap
variable {A : Atlas X I} {B : Atlas Y J} {f : Y ⟶ X} (r : AtlasMap A B f)

private theorem pair_w (i j : J) :
    embedding.map (B.left i j ≫ r.chart i) ≫ A.chart (r.index i) =
      embedding.map (B.right i j ≫ r.chart j) ≫ A.chart (r.index j) := by
  simp only [Functor.map_comp, Category.assoc, r.commutes]
  exact congrArg (fun h => h ≫ f) (B.square i j).w

def pair (i j : J) : B.pair i j ⟶ A.pair (r.index i) (r.index j) :=
  (homEquiv _ _).symm ((A.square (r.index i) (r.index j)).lift
    (embedding.map (B.left i j ≫ r.chart i))
    (embedding.map (B.right i j ≫ r.chart j)) (r.pair_w i j))

theorem pair_map (i j : J) : embedding.map (r.pair i j) =
    (A.square (r.index i) (r.index j)).lift
      (embedding.map (B.left i j ≫ r.chart i))
      (embedding.map (B.right i j ≫ r.chart j)) (r.pair_w i j) := forward_inverse _

@[simp, reassoc] theorem pair_left (i j : J) :
    r.pair i j ≫ A.left (r.index i) (r.index j) = B.left i j ≫ r.chart i := by
  apply (homEquiv _ _).injective
  change embedding.map (_ ≫ _) = embedding.map _
  rw [Functor.map_comp, r.pair_map]
  simp

@[simp, reassoc] theorem pair_right (i j : J) :
    r.pair i j ≫ A.right (r.index i) (r.index j) = B.right i j ≫ r.chart j := by
  apply (homEquiv _ _).injective
  change embedding.map (_ ≫ _) = embedding.map _
  rw [Functor.map_comp, r.pair_map]
  simp

private theorem triple_w (i j k : J) :
    embedding.map (B.firstSecond i j k ≫ r.pair i j) ≫
      (embedding.map (A.left (r.index i) (r.index j)) ≫ A.chart (r.index i)) =
    embedding.map (B.third i j k ≫ r.chart k) ≫ A.chart (r.index k) := by
  have h : embedding.map (r.pair i j) ≫
      embedding.map (A.left (r.index i) (r.index j)) ≫ A.chart (r.index i) =
      embedding.map (B.left i j) ≫ B.chart i ≫ f := by
    rw [← Category.assoc, ← Functor.map_comp, r.pair_left,
      Functor.map_comp, Category.assoc, r.commutes]
  simp only [Functor.map_comp, Category.assoc]
  rw [h, r.commutes]
  simpa only [Category.assoc] using congrArg (fun h => h ≫ f) (B.triple_isPullback i j k).w

def triple (i j k : J) : B.triple i j k ⟶ A.triple (r.index i) (r.index j) (r.index k) :=
  (homEquiv _ _).symm ((A.triple_isPullback (r.index i) (r.index j) (r.index k)).lift
    (embedding.map (B.firstSecond i j k ≫ r.pair i j))
    (embedding.map (B.third i j k ≫ r.chart k)) (r.triple_w i j k))

theorem triple_map (i j k : J) : embedding.map (r.triple i j k) =
    (A.triple_isPullback (r.index i) (r.index j) (r.index k)).lift
      (embedding.map (B.firstSecond i j k ≫ r.pair i j))
      (embedding.map (B.third i j k ≫ r.chart k)) (r.triple_w i j k) := forward_inverse _

@[simp, reassoc] theorem triple_firstSecond (i j k : J) :
    r.triple i j k ≫ A.firstSecond (r.index i) (r.index j) (r.index k) =
      B.firstSecond i j k ≫ r.pair i j := by
  apply (homEquiv _ _).injective
  change embedding.map (_ ≫ _) = embedding.map _
  rw [Functor.map_comp, r.triple_map]
  simp

@[simp, reassoc] theorem triple_third (i j k : J) :
    r.triple i j k ≫ A.third (r.index i) (r.index j) (r.index k) =
      B.third i j k ≫ r.chart k := by
  apply (homEquiv _ _).injective
  change embedding.map (_ ≫ _) = embedding.map _
  rw [Functor.map_comp, r.triple_map]
  simp

private theorem pair_ext {D : Domain} {i j : I} (u v : D ⟶ A.pair i j)
    (hl : u ≫ A.left i j = v ≫ A.left i j)
    (hr : u ≫ A.right i j = v ≫ A.right i j) : u = v := by
  apply (homEquiv _ _).injective
  change embedding.map u = embedding.map v
  apply (A.square i j).hom_ext
  · simpa only [Functor.map_comp] using congrArg embedding.map hl
  · simpa only [Functor.map_comp] using congrArg embedding.map hr

@[simp, reassoc] theorem diagonal_pair (i : J) :
    B.diagonal i ≫ r.pair i i = r.chart i ≫ A.diagonal (r.index i) := by
  apply pair_ext
  · simp only [Category.assoc, r.pair_left, A.diagonal_left, Category.comp_id]
    rw [← Category.assoc, B.diagonal_left, Category.id_comp]
  · simp only [Category.assoc, r.pair_right, A.diagonal_right, Category.comp_id]
    rw [← Category.assoc, B.diagonal_right, Category.id_comp]

@[simp, reassoc] theorem triple_firstThird (i j k : J) :
    r.triple i j k ≫ A.firstThird (r.index i) (r.index j) (r.index k) =
      B.firstThird i j k ≫ r.pair i k := by
  apply pair_ext
  · simp only [Category.assoc, A.firstThird_left, r.pair_left]
    simp only [← Category.assoc, r.triple_firstSecond, B.firstThird_left]
    simp only [Category.assoc, r.pair_left]
  · simp only [Category.assoc, A.firstThird_right, r.pair_right]
    simp only [← Category.assoc, r.triple_third, B.firstThird_right]

@[simp, reassoc] theorem triple_secondThird (i j k : J) :
    r.triple i j k ≫ A.secondThird (r.index i) (r.index j) (r.index k) =
      B.secondThird i j k ≫ r.pair j k := by
  apply pair_ext
  · simp only [Category.assoc, A.secondThird_left, r.pair_left]
    simp only [← Category.assoc, r.triple_firstSecond, B.secondThird_left]
    simp only [Category.assoc, r.pair_right]
  · simp only [Category.assoc, A.secondThird_right, r.pair_right]
    simp only [← Category.assoc, r.triple_third, B.secondThird_right]

/-- The atlas map induces the actual map between sheaf coproduct covers. -/
def total : B.total ⟶ A.total :=
  SheafCoproductLocal.desc B.family (fun j => embedding.map (r.chart j) ≫ A.inclusion (r.index j))

@[simp, reassoc] theorem inclusion_total (j : J) :
    B.inclusion j ≫ r.total = embedding.map (r.chart j) ≫ A.inclusion (r.index j) :=
  SheafCoproductLocal.inclusion_desc _ _ _

theorem total_cover : r.total ≫ A.cover = B.cover ≫ f := by
  apply colimit.hom_ext
  intro ⟨j⟩
  change B.inclusion j ≫ _ = B.inclusion j ≫ _
  rw [← Category.assoc, r.inclusion_total, Category.assoc, A.inclusion_cover,
    r.commutes, ← Category.assoc, B.inclusion_cover]

end AtlasMap
end SquareKit.SmoothRepresentedCover

open scoped Manifold ContDiff
namespace SquareKit.SmoothCech
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothRepresentedCover SmoothManifoldAction
open ManifoldRealization
variable {X Y : Sheaf topology Type} {I J : Type} {A : Atlas X I} {B : Atlas Y J}
variable {f : Y ⟶ X} (r : AtlasMap A B f)
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]

private theorem map_apply_eq {U V W : Domain} {a : U ⟶ V} {b : V ⟶ W}
    {c : U ⟶ W} (h : a ≫ b = c) (x : Points U) :
    (show EuclideanOpen.Map _ _ from b) ((show EuclideanOpen.Map _ _ from a) x) =
      (show EuclideanOpen.Map _ _ from c) x :=
  congrArg (fun z : U ⟶ W => (show EuclideanOpen.Map _ _ from z) x) h

namespace Datum
variable (p : Datum (d := d) (G := G) (M := M) A)

def restrict : Datum (d := d) (G := G) (M := M) B where
  localMap j := (p.localMap (r.index j)).restrict (r.chart j)
  transition i j := ⟨restrictLabel (p.transition (r.index i) (r.index j)).val (r.pair i j), fun x => by
    have hl := map_apply_eq (r.pair_left i j) x
    have hr := map_apply_eq (r.pair_right i j) x
    have ht := (p.transition (r.index i) (r.index j)).property
      ((show EuclideanOpen.Map _ _ from r.pair i j) x)
    change (p.transition (r.index i) (r.index j)).val _ •
      (p.localMap (r.index i)).val ((show EuclideanOpen.Map _ _ from A.left _ _)
        ((show EuclideanOpen.Map _ _ from r.pair i j) x)) =
      (p.localMap (r.index j)).val ((show EuclideanOpen.Map _ _ from A.right _ _)
        ((show EuclideanOpen.Map _ _ from r.pair i j) x)) at ht
    erw [hl, hr] at ht
    exact ht⟩
  diagonal i x := by
    have h := map_apply_eq (r.diagonal_pair i) x
    change (p.transition (r.index i) (r.index i)).val
      ((show EuclideanOpen.Map _ _ from r.pair i i)
        ((show EuclideanOpen.Map _ _ from B.diagonal i) x)) = 1
    erw [h]
    exact p.diagonal (r.index i) ((show EuclideanOpen.Map _ _ from r.chart i) x)
  cocycle i j k x := by
    have h₁ := map_apply_eq (r.triple_firstThird i j k) x
    have h₂ := map_apply_eq (r.triple_secondThird i j k) x
    have h₃ := map_apply_eq (r.triple_firstSecond i j k) x
    have h := p.cocycle (r.index i) (r.index j) (r.index k)
      ((show EuclideanOpen.Map _ _ from r.triple i j k) x)
    erw [h₁, h₂, h₃] at h
    exact h

end Datum

namespace Hom
variable {p q : Datum (d := d) (G := G) (M := M) A}

def restrict (h : Hom p q) : Hom (p.restrict r) (q.restrict r) where
  labels j := ⟨restrictLabel (h.labels (r.index j)).val (r.chart j), fun x =>
    (h.labels (r.index j)).property ((show EuclideanOpen.Map _ _ from r.chart j) x)⟩
  commutes i j x := by
    have hl := map_apply_eq (r.pair_left i j) x
    have hr := map_apply_eq (r.pair_right i j) x
    have he := h.commutes (r.index i) (r.index j)
      ((show EuclideanOpen.Map _ _ from r.pair i j) x)
    erw [hl, hr] at he
    exact he

omit [IsManifold (modelWithCorners d) ∞ M] in
theorem restrict_ident (p : Datum (d := d) (G := G) (M := M) A) :
    (Hom.ident p).restrict r = Hom.ident (p.restrict r) := by
  apply Hom.ext
  funext j
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  rfl

omit [IsManifold (modelWithCorners d) ∞ M] in
theorem restrict_comp {s : Datum (d := d) (G := G) (M := M) A}
    (h : Hom p q) (k : Hom q s) : (h.comp k).restrict r = (h.restrict r).comp (k.restrict r) := by
  apply Hom.ext
  funext j
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  rfl

omit [IsManifold (modelWithCorners d) ∞ M] in
theorem restrict_inverse (h : Hom p q) : h.inverse.restrict r = (h.restrict r).inverse := by
  apply Hom.ext
  funext j
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  rfl

end Hom

/-- Restriction preserves all external arrows and their groupoid operations. -/
def restriction : Datum (d := d) (G := G) (M := M) A ⥤
    Datum (d := d) (G := G) (M := M) B where
  obj p := p.restrict r
  map h := h.restrict r
  map_id := Hom.restrict_ident r
  map_comp := Hom.restrict_comp r

end SquareKit.SmoothCech

namespace SquareKit.SmoothRepresentedCover.AtlasMap
open CategoryTheory CategoryTheory.Limits EuclideanOpen SmoothOpenSite
variable {X Y Z : Sheaf topology Type} {I J K : Type}
  (A : Atlas X I) {B : Atlas Y J} {C : Atlas Z K}

def ident : AtlasMap A A (𝟙 X) where
  index := id
  chart _ := 𝟙 _
  commutes _ := by simp

variable {A}
def comp {f : Y ⟶ X} {g : Z ⟶ Y} (r : AtlasMap A B f) (s : AtlasMap B C g) :
    AtlasMap A C (g ≫ f) where
  index k := r.index (s.index k)
  chart k := s.chart k ≫ r.chart (s.index k)
  commutes k := by
    rw [Functor.map_comp, Category.assoc, r.commutes]
    rw [← Category.assoc, s.commutes, Category.assoc]

@[simp] theorem ident_pair (i j : I) : (ident A).pair i j = 𝟙 (A.pair i j) := by
  apply pair_ext
  · simpa only [ident, id_eq, Category.comp_id, Category.id_comp] using (ident A).pair_left i j
  · simpa only [ident, id_eq, Category.comp_id, Category.id_comp] using (ident A).pair_right i j

@[simp] theorem comp_pair {f : Y ⟶ X} {g : Z ⟶ Y}
    (r : AtlasMap A B f) (s : AtlasMap B C g) (i j : K) :
    (r.comp s).pair i j = s.pair i j ≫ r.pair (s.index i) (s.index j) := by
  apply pair_ext
  · simp only [pair_left, comp, Category.assoc, pair_left_assoc]
  · simp only [pair_right, comp, Category.assoc, pair_right_assoc]

@[simp] theorem ident_total : (ident A).total = 𝟙 A.total := by
  apply colimit.hom_ext
  intro ⟨i⟩
  change A.inclusion i ≫ (ident A).total = A.inclusion i ≫ 𝟙 A.total
  rw [inclusion_total]
  simp [ident]

@[simp] theorem comp_total {f : Y ⟶ X} {g : Z ⟶ Y}
    (r : AtlasMap A B f) (s : AtlasMap B C g) : (r.comp s).total = s.total ≫ r.total := by
  apply colimit.hom_ext
  intro ⟨i⟩
  change C.inclusion i ≫ (r.comp s).total = C.inclusion i ≫ s.total ≫ r.total
  rw [inclusion_total, ← Category.assoc, inclusion_total, Category.assoc, inclusion_total]
  simp only [comp, Functor.map_comp, Category.assoc]

end SquareKit.SmoothRepresentedCover.AtlasMap

open scoped Manifold ContDiff
namespace SquareKit.SmoothCech.Datum
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothRepresentedCover SmoothManifoldAction
open ManifoldRealization
variable {X Y Z : Sheaf topology Type} {I J K : Type}
  {A : Atlas X I} {B : Atlas Y J} {C : Atlas Z K}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]

omit [IsManifold (modelWithCorners d) ∞ M] in
theorem restrict_ident (p : Datum (d := d) (G := G) (M := M) A) :
    p.restrict (AtlasMap.ident A) = p := by
  apply Datum.ext
  · funext i
    apply Subtype.ext
    rfl
  · apply heq_of_eq
    funext i j
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    change (p.transition i j).val
      ((show EuclideanOpen.Map _ _ from (AtlasMap.ident A).pair i j) x) = _
    rw [AtlasMap.ident_pair]
    rfl

omit [IsManifold (modelWithCorners d) ∞ M] in
theorem restrict_comp (p : Datum (d := d) (G := G) (M := M) A)
    {f : Y ⟶ X} {g : Z ⟶ Y} (r : AtlasMap A B f) (s : AtlasMap B C g) :
    (p.restrict r).restrict s = p.restrict (r.comp s) := by
  apply Datum.ext
  · funext i
    apply Subtype.ext
    rfl
  · apply heq_of_eq
    funext i j
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    change (p.transition (r.index (s.index i)) (r.index (s.index j))).val
      ((show EuclideanOpen.Map _ _ from r.pair (s.index i) (s.index j))
        ((show EuclideanOpen.Map _ _ from s.pair i j) x)) =
      (p.transition (r.index (s.index i)) (r.index (s.index j))).val
        ((show EuclideanOpen.Map _ _ from (r.comp s).pair i j) x)
    rw [AtlasMap.comp_pair]
    rfl

end SquareKit.SmoothCech.Datum

namespace SquareKit.SmoothRepresentedCover.AtlasMap
open CategoryTheory CategoryTheory.Limits EuclideanOpen SmoothOpenSite
variable {X Y : Sheaf topology Type} {I J : Type}
  {A : Atlas X I} {B : Atlas Y J} {f : Y ⟶ X} (r : AtlasMap A B f)

@[simp, reassoc] theorem pairMap_double (i j : J) :
    B.pairMap i j ≫ SheafCoverCech.mapDouble f r.total r.total_cover =
      embedding.map (r.pair i j) ≫ A.pairMap (r.index i) (r.index j) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, SheafCoverCech.mapDouble_first, A.pairMap_first,
      B.pairMap_first_assoc, inclusion_total]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun h => embedding.map h ≫ A.inclusion (r.index i)) (r.pair_left i j).symm
  · simp only [Category.assoc, SheafCoverCech.mapDouble_second, A.pairMap_second,
      B.pairMap_second_assoc, inclusion_total]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun h => embedding.map h ≫ A.inclusion (r.index j)) (r.pair_right i j).symm

end SquareKit.SmoothRepresentedCover.AtlasMap

open scoped Manifold ContDiff
namespace SquareKit.SmoothCech.Datum
open CategoryTheory CategoryTheory.Limits EuclideanOpen SmoothOpenSite SmoothRepresentedCover
open SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X Y : Sheaf topology Type} {I J : Type} {A : Atlas X I} {B : Atlas Y J}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (p : Datum (d := d) (G := G) (M := M) A)
  {f : Y ⟶ X} (r : AtlasMap A B f)

theorem restrict_localMapSheaf : (p.restrict r).localMapSheaf = r.total ≫ p.localMapSheaf := by
  apply colimit.hom_ext
  intro ⟨j⟩
  change B.inclusion j ≫ (p.restrict r).localMapSheaf = B.inclusion j ≫ r.total ≫ p.localMapSheaf
  rw [localMapSheaf_fac, ← Category.assoc, r.inclusion_total, Category.assoc, localMapSheaf_fac]
  exact (External.hat_restrict (p.localMap (r.index j)) (r.chart j)).symm

variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

theorem restrict_overlapLabel : (p.restrict r).overlapLabel smoothAction =
    SheafCoverCech.mapDouble f r.total r.total_cover ≫ p.overlapLabel smoothAction := by
  apply B.pairHom_ext
  intro i j
  rw [overlapLabel_fac, ← Category.assoc, r.pairMap_double, Category.assoc, overlapLabel_fac]
  apply (ordinaryHomLabelEquiv G (B.pair i j)).injective
  apply LocallyConstant.ext
  intro x
  rw [ordinaryHomLabelEquiv_natural, transitionArrow_label, transitionArrow_label]
  rfl

end SquareKit.SmoothCech.Datum

namespace SquareKit.SmoothRepresentedCover.AtlasMap
open CategoryTheory CategoryTheory.Limits EuclideanOpen SmoothOpenSite
variable {X Y : Sheaf topology Type} {I J : Type}
  {A : Atlas X I} {B : Atlas Y J} {f : Y ⟶ X} (r : AtlasMap A B f)

/-- The map of actual covers, expressed in the selected split displays. -/
def splitTotal : SplitSheaf.extension (SplitSheaf.ofDisplay B.cover) ⟶
    SplitSheaf.extension (SplitSheaf.ofDisplay A.cover) :=
  (SplitSheaf.displayIso B.cover).hom ≫ r.total ≫ (SplitSheaf.displayIso A.cover).inv

theorem splitTotal_cover : r.splitTotal ≫ SplitSheaf.p (SplitSheaf.ofDisplay A.cover) =
    SplitSheaf.p (SplitSheaf.ofDisplay B.cover) ≫ f := by
  rw [splitTotal, ← SplitSheaf.displayIso_projection A.cover]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [r.total_cover, ← Category.assoc, SplitSheaf.displayIso_projection]

end SquareKit.SmoothRepresentedCover.AtlasMap

open scoped Manifold ContDiff
namespace SquareKit.SmoothCech.Datum
open CategoryTheory CategoryTheory.Limits EuclideanOpen SmoothOpenSite SmoothRepresentedCover
open SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X Y : Sheaf topology Type} {I J : Type} {A : Atlas X I} {B : Atlas Y J}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (p : Datum (d := d) (G := G) (M := M) A)
  {f : Y ⟶ X} (r : AtlasMap A B f)

theorem restrict_splitLocalMap : (p.restrict r).splitLocalMap = r.splitTotal ≫ p.splitLocalMap := by
  simp only [splitLocalMap, AtlasMap.splitTotal, Category.assoc, Iso.inv_hom_id_assoc]
  rw [restrict_localMapSheaf]

variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

theorem restrict_localObject : ((p.restrict r).cech smoothAction).localObject =
    reindex (p.cech smoothAction).localObject r.splitTotal := by
  change chart _ _ = reindex (chart _ _) _
  rw [chart_reindex, restrict_splitLocalMap]

/-- The selected comparison is pulled along the actual map of covers. No
pullback property is imposed on the total atlas map. -/
def restrictLocalComparison : Arrow
    (reindex (reindex (p.interpreted smoothAction) f) (SplitSheaf.p (SplitSheaf.ofDisplay B.cover)))
    ((p.restrict r).cech smoothAction).localObject :=
  (eqToHom (congrArg (fun k => reindex (p.interpreted smoothAction) k) r.splitTotal_cover.symm)).comp
    (((p.cech smoothAction).toDescent.comparison.reindex r.splitTotal).comp
      (eqToHom (p.restrict_localObject r smoothAction).symm))

end SquareKit.SmoothCech.Datum

namespace SquareKit.SmoothRepresentedCover.AtlasMap
open CategoryTheory CategoryTheory.Limits EuclideanOpen SmoothOpenSite
variable {X Y : Sheaf topology Type} {I J : Type}
  {A : Atlas X I} {B : Atlas Y J} {f : Y ⟶ X} (r : AtlasMap A B f)

def splitDouble : SplitSheaf.Cech.double (SplitSheaf.ofDisplay B.cover) ⟶
    SplitSheaf.Cech.double (SplitSheaf.ofDisplay A.cover) :=
  (SheafCoverCech.splitDoubleIso B.cover).hom ≫
    SheafCoverCech.mapDouble f r.total r.total_cover ≫ (SheafCoverCech.splitDoubleIso A.cover).inv

@[simp, reassoc] theorem splitDouble_first :
    r.splitDouble ≫ SplitSheaf.Cech.first (SplitSheaf.ofDisplay A.cover) =
      SplitSheaf.Cech.first (SplitSheaf.ofDisplay B.cover) ≫ r.splitTotal := by
  apply (cancel_mono (SplitSheaf.displayIso A.cover).hom).1
  simp only [splitDouble, splitTotal, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← SheafCoverCech.splitDouble_first A.cover]
  simp only [Iso.inv_hom_id_assoc, SheafCoverCech.mapDouble_first,
    SheafCoverCech.splitDouble_first_assoc]

@[simp, reassoc] theorem splitDouble_second :
    r.splitDouble ≫ SplitSheaf.Cech.second (SplitSheaf.ofDisplay A.cover) =
      SplitSheaf.Cech.second (SplitSheaf.ofDisplay B.cover) ≫ r.splitTotal := by
  apply (cancel_mono (SplitSheaf.displayIso A.cover).hom).1
  simp only [splitDouble, splitTotal, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← SheafCoverCech.splitDouble_second A.cover]
  simp only [Iso.inv_hom_id_assoc, SheafCoverCech.mapDouble_second,
    SheafCoverCech.splitDouble_second_assoc]

end SquareKit.SmoothRepresentedCover.AtlasMap

open scoped Manifold ContDiff
namespace SquareKit.SmoothCech.Datum
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothRepresentedCover
open SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X Y : Sheaf topology Type} {I J : Type} {A : Atlas X I} {B : Atlas Y J}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (p : Datum (d := d) (G := G) (M := M) A)
  {f : Y ⟶ X} (r : AtlasMap A B f)
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

theorem restrict_splitLabel : (p.restrict r).splitLabel smoothAction =
    r.splitDouble ≫ p.splitLabel smoothAction := by
  simp only [splitLabel, AtlasMap.splitDouble, Category.assoc, Iso.inv_hom_id_assoc]
  rw [restrict_overlapLabel]

end SquareKit.SmoothCech.Datum

namespace SquareKit.SheafActionQuotient.Descent
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M X : Sheaf J (Type (max u v))}
variable {a : Action G M} {A : SplitSheaf.Ty X}
variable [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]

theorem Datum.comparison_overlap (d : Datum (a := a) A) :
    (d.comparison.reindex (SplitSheaf.Cech.first A)).comp d.overlapArrow =
      d.comparison.reindex (SplitSheaf.Cech.second A) := by
  apply Arrow.ext
  apply SheafTorsor.Arrow.ext
  ext x p
  exact SheafTorsor.Descent.evaluation_transport d.torsorDatum
    (X.obj.elementsMk x.obj x.val.1.1) x.val.1.2 x.val.2 p

end SquareKit.SheafActionQuotient.Descent


section SelectedRefinement
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
namespace SquareKit.SmoothCech.Datum
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothRepresentedCover
open SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X Y : Sheaf topology Type} {I J : Type} {A : Atlas X I} {B : Atlas Y J}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (p : Datum (d := d) (G := G) (M := M) A)
  {f : Y ⟶ X} (r : AtlasMap A B f)
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

theorem restrictLocalComparison_heq :
    HEq (p.restrictLocalComparison r smoothAction)
      ((p.cech smoothAction).toDescent.comparison.reindex r.splitTotal) := by
  unfold restrictLocalComparison
  exact (eqToHom_comp_heq (C := Object (representation smoothAction).action
    (SplitSheaf.extension (SplitSheaf.ofDisplay B.cover))) _ _).trans
      (comp_eqToHom_heq (C := Object (representation smoothAction).action
        (SplitSheaf.extension (SplitSheaf.ofDisplay B.cover))) _ _)

theorem restrict_overlap_heq :
    HEq ((p.restrict r).cech smoothAction).overlap.hom
      (((p.cech smoothAction).overlap.hom).reindex r.splitDouble) := by
  have aux {Z : Sheaf topology Type}
      (v w v' w' : Z ⟶ object d M) (k k' : Z ⟶ locallyConstantGroupSheaf G)
      (hv : v = v') (hw : w = w') (hk : k = k')
      (h : (representation smoothAction).action.onMap k w = v)
      (h' : (representation smoothAction).action.onMap k' w' = v') :
      HEq (chartArrowOfRelation k v w h) (chartArrowOfRelation k' v' w' h') := by
    cases hv; cases hw; cases hk
    rfl
  have hr : (((p.cech smoothAction).overlap.hom).reindex r.splitDouble) =
      chartArrowOfRelation (a := (representation smoothAction).action)
        (r.splitDouble ≫ p.splitLabel smoothAction)
        (r.splitDouble ≫ SplitSheaf.Cech.first _ ≫ p.splitLocalMap)
        (r.splitDouble ≫ SplitSheaf.Cech.second _ ≫ p.splitLocalMap)
        (by simpa only [onMap_precomp] using (congrArg (fun v => r.splitDouble ≫ v)
          (p.splitLabel_relation smoothAction))) := by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    rfl
  rw [hr]
  exact aux _ _ _ _ _ _
    (by simp only [restrict_splitLocalMap, r.splitDouble_first_assoc])
    (by simp only [restrict_splitLocalMap, r.splitDouble_second_assoc])
    (p.restrict_splitLabel r smoothAction)
    ((p.restrict r).splitLabel_relation smoothAction)
    (by simpa only [onMap_precomp] using (congrArg (fun v => r.splitDouble ≫ v)
      (p.splitLabel_relation smoothAction)))

theorem restrictLocalComparison_overlap :
    ((p.restrictLocalComparison r smoothAction).reindex
      (SplitSheaf.Cech.first (SplitSheaf.ofDisplay B.cover))).comp
      ((p.restrict r).cech smoothAction).overlap.hom =
    (p.restrictLocalComparison r smoothAction).reindex
      (SplitSheaf.Cech.second (SplitSheaf.ofDisplay B.cover)) := by
  let P := p.interpreted smoothAction
  let c := (p.cech smoothAction).toDescent.comparison
  let e := p.restrictLocalComparison r smoothAction
  have aux {V W : Sheaf topology Type}
      {P Q P' Q' : Object (representation smoothAction).action V}
      (hP : P = P') (hQ : Q = Q') (a : Arrow P Q) (b : Arrow P' Q')
      (h : HEq a b) (k : W ⟶ V) : HEq (a.reindex k) (b.reindex k) := by
    cases hP; cases hQ; cases h
    rfl
  have assoc {V W Z : Sheaf topology Type}
      {P Q : Object (representation smoothAction).action V}
      (a : Arrow P Q) (k : W ⟶ V) (l : Z ⟶ W) :
      HEq ((a.reindex k).reindex l) (a.reindex (l ≫ k)) := by rfl
  have changeMap (k l : SplitSheaf.Cech.double (SplitSheaf.ofDisplay B.cover) ⟶
      SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)) (h : k = l) :
      HEq (c.reindex k) (c.reindex l) := by
    cases h
    rfl
  have hs : reindex (reindex P f) (SplitSheaf.p (SplitSheaf.ofDisplay B.cover)) =
      reindex (reindex P (SplitSheaf.p (SplitSheaf.ofDisplay A.cover))) r.splitTotal := by
    simp only [reindex_comp]
    exact congrArg (reindex P) r.splitTotal_cover.symm
  have hfirst : HEq (e.reindex (SplitSheaf.Cech.first (SplitSheaf.ofDisplay B.cover)))
      (c.reindex (r.splitDouble ≫ SplitSheaf.Cech.first (SplitSheaf.ofDisplay A.cover))) := by
    exact (aux hs (p.restrict_localObject r smoothAction) e (c.reindex r.splitTotal)
      (p.restrictLocalComparison_heq r smoothAction)
      (SplitSheaf.Cech.first (SplitSheaf.ofDisplay B.cover))).trans
      ((assoc c r.splitTotal (SplitSheaf.Cech.first (SplitSheaf.ofDisplay B.cover))).trans
        (changeMap _ _ r.splitDouble_first.symm))
  have hsecond : HEq (e.reindex (SplitSheaf.Cech.second (SplitSheaf.ofDisplay B.cover)))
      (c.reindex (r.splitDouble ≫ SplitSheaf.Cech.second (SplitSheaf.ofDisplay A.cover))) := by
    exact (aux hs (p.restrict_localObject r smoothAction) e (c.reindex r.splitTotal)
      (p.restrictLocalComparison_heq r smoothAction)
      (SplitSheaf.Cech.second (SplitSheaf.ofDisplay B.cover))).trans
      ((assoc c r.splitTotal (SplitSheaf.Cech.second (SplitSheaf.ofDisplay B.cover))).trans
        (changeMap _ _ r.splitDouble_second.symm))
  have hsource :
      reindex (reindex (reindex P f) (SplitSheaf.p (SplitSheaf.ofDisplay B.cover)))
        (SplitSheaf.Cech.first (SplitSheaf.ofDisplay B.cover)) =
      reindex (reindex P (SplitSheaf.p (SplitSheaf.ofDisplay A.cover)))
        (r.splitDouble ≫ SplitSheaf.Cech.first (SplitSheaf.ofDisplay A.cover)) := by
    simp only [reindex_comp, r.splitDouble_first, Category.assoc, r.splitTotal_cover]
  have hlocal (k : Bool) :
      reindex ((p.restrict r).cech smoothAction).localObject
        (if k then SplitSheaf.Cech.first _ else SplitSheaf.Cech.second _) =
      reindex (p.cech smoothAction).localObject
        (r.splitDouble ≫ (if k then SplitSheaf.Cech.first _ else SplitSheaf.Cech.second _)) := by
    rw [p.restrict_localObject r smoothAction]
    cases k
    · simp only [Bool.false_eq_true, ↓reduceIte, reindex_comp, r.splitDouble_second]
    · simp only [↓reduceIte, reindex_comp, r.splitDouble_first]
  have ho : (p.cech smoothAction).toDescent.overlapArrow =
      (p.cech smoothAction).overlap.hom := by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    rfl
  have hc0 := (p.cech smoothAction).toDescent.comparison_overlap
  rw [ho] at hc0
  have hc := congrArg (fun h => h.reindex r.splitDouble) hc0
  have hh := CategoryTheory.heq_comp hsource (hlocal true) (hlocal false)
    hfirst (p.restrict_overlap_heq r smoothAction)
  exact eq_of_heq (hh.trans ((heq_of_eq hc).trans hsecond.symm))

/-- The actual map of covers yields a compatible map out of canonical descent.
The transport equation follows from the selected original comparison. -/
def restrictDescentMap : Descent.Map
    (Descent.canonicalDatum (SplitSheaf.ofDisplay B.cover)
      (reindex (p.interpreted smoothAction) f))
    ((p.restrict r).cech smoothAction).toDescent where
  torsorMap := {
    hom := (p.restrictLocalComparison r smoothAction).torsorArrow.iso.hom
    equivariant := (p.restrictLocalComparison r smoothAction).torsorArrow.equivariant
    transport x b c z := (congrArg (fun k => k.torsorArrow.iso.hom.app
      ((SplitSheaf.Cech.double (SplitSheaf.ofDisplay B.cover)).obj.elementsMk x.obj
        ⟨⟨x.val,b⟩,c⟩) z) (p.restrictLocalComparison_overlap r smoothAction)).symm }
  preserves := (p.restrictLocalComparison r smoothAction).preserves

/-- Selected comparison between restriction of the interpreted quotient and
interpretation on the actual refined atlas. -/
def restrictComparison : Arrow (reindex (p.interpreted smoothAction) f)
    ((p.restrict r).interpreted smoothAction) :=
  (Descent.canonicalEmbedding (SplitSheaf.ofDisplay B.cover)
    (reindex (p.interpreted smoothAction) f)).comp
    (p.restrictDescentMap r smoothAction).arrow

/-- The global comparison recovers the selected local comparison exactly. -/
theorem restrictComparison_recover :
    ((p.restrictComparison r smoothAction).reindex
      (SplitSheaf.p (SplitSheaf.ofDisplay B.cover))).comp
      ((p.restrict r).cech smoothAction).toDescent.comparison =
    p.restrictLocalComparison r smoothAction := by
  apply SheafActionQuotient.Arrow.ext
  apply SheafTorsor.Arrow.ext
  ext x z
  have he := (p.restrictDescentMap r smoothAction).torsorMap.evaluation
    (Y.obj.elementsMk x.obj x.val.1) x.val.2
    ((SheafTorsor.Descent.canonicalEmbedding (SplitSheaf.ofDisplay B.cover)
      (reindex (p.interpreted smoothAction) f).torsor).hom.app
      (Y.obj.elementsMk x.obj x.val.1) z)
  have hc := congrArg (fun h => h.iso.hom.app x z)
    (SheafTorsor.Descent.canonicalEmbedding_evaluation (SplitSheaf.ofDisplay B.cover)
      (reindex (p.interpreted smoothAction) f).torsor)
  exact he.trans (congrArg ((p.restrictDescentMap r smoothAction).torsorMap.hom.app x) hc)

end SquareKit.SmoothCech.Datum
namespace SquareKit.SmoothCech.Hom
open CategoryTheory CategoryTheory.Limits EuclideanOpen SmoothOpenSite SmoothRepresentedCover
open SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X Y : Sheaf topology Type} {I J : Type} {A : Atlas X I} {B : Atlas Y J}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable {p q : Datum (d := d) (G := G) (M := M) A}
  (h : Hom p q) {f : Y ⟶ X} (r : AtlasMap A B f)
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

theorem restrict_localLabel : (h.restrict r).localLabel smoothAction =
    r.total ≫ h.localLabel smoothAction := by
  apply colimit.hom_ext
  intro ⟨j⟩
  change B.inclusion j ≫ _ = B.inclusion j ≫ _
  rw [localLabel_fac, ← Category.assoc, r.inclusion_total, Category.assoc, localLabel_fac]
  apply (ordinaryHomLabelEquiv G (B.domain j)).injective
  apply LocallyConstant.ext
  intro x
  rw [ordinaryHomLabelEquiv_natural, chartArrow_label, chartArrow_label]
  rfl

theorem restrict_splitLabel : (h.restrict r).splitLabel smoothAction =
    r.splitTotal ≫ h.splitLabel smoothAction := by
  simp only [splitLabel, AtlasMap.splitTotal, Category.assoc, Iso.inv_hom_id_assoc]
  rw [restrict_localLabel]

theorem restrict_localArrow_heq : HEq ((h.restrict r).localArrow smoothAction)
    ((h.localArrow smoothAction).reindex r.splitTotal) := by
  have aux {Z : Sheaf topology Type}
      (v w v' w' : Z ⟶ object d M) (k k' : Z ⟶ locallyConstantGroupSheaf G)
      (hv : v = v') (hw : w = w') (hk : k = k')
      (h : (representation smoothAction).action.onMap k w = v)
      (h' : (representation smoothAction).action.onMap k' w' = v') :
      HEq (chartArrowOfRelation k v w h) (chartArrowOfRelation k' v' w' h') := by
    cases hv; cases hw; cases hk
    rfl
  have hr : (h.localArrow smoothAction).reindex r.splitTotal =
      chartArrowOfRelation (a := (representation smoothAction).action)
        (r.splitTotal ≫ h.splitLabel smoothAction)
        (r.splitTotal ≫ p.splitLocalMap) (r.splitTotal ≫ q.splitLocalMap)
        (by simpa only [Datum.onMap_precomp] using (congrArg (fun v => r.splitTotal ≫ v)
          (h.splitLabel_relation smoothAction))) := by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    rfl
  rw [hr]
  exact aux _ _ _ _ _ _ (p.restrict_splitLocalMap r) (q.restrict_splitLocalMap r)
    (h.restrict_splitLabel r smoothAction)
    ((h.restrict r).splitLabel_relation smoothAction)
    (by simpa only [Datum.onMap_precomp] using (congrArg (fun v => r.splitTotal ≫ v)
      (h.splitLabel_relation smoothAction)))

theorem interpreted_comparison :
    ((h.interpreted smoothAction).reindex (SplitSheaf.p (SplitSheaf.ofDisplay A.cover))).comp
      (q.cech smoothAction).toDescent.comparison =
    (p.cech smoothAction).toDescent.comparison.comp (h.localArrow smoothAction) := by
  have he : (h.cechMap smoothAction).toDescent.localArrow = h.localArrow smoothAction := by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    rfl
  have hn := Descent.Map.comparison_naturality (representation smoothAction).action
    (SplitSheaf.ofDisplay A.cover) (h.cechMap smoothAction).toDescent
  rw [he] at hn
  exact hn

end SquareKit.SmoothCech.Hom
namespace SquareKit.SmoothCech.Hom
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothRepresentedCover
open SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X Y : Sheaf topology Type} {I J : Type} {A : Atlas X I} {B : Atlas Y J}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable {p q : Datum (d := d) (G := G) (M := M) A}
  (h : Hom p q) {f : Y ⟶ X} (r : AtlasMap A B f)
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

theorem restrictLocalComparison_naturality :
    (((h.interpreted smoothAction).reindex f).reindex
      (SplitSheaf.p (SplitSheaf.ofDisplay B.cover))).comp
      (q.restrictLocalComparison r smoothAction) =
    (p.restrictLocalComparison r smoothAction).comp ((h.restrict r).localArrow smoothAction) := by
  have hs (v : Datum (d := d) (G := G) (M := M) A) :
      reindex (reindex (v.interpreted smoothAction) f)
        (SplitSheaf.p (SplitSheaf.ofDisplay B.cover)) =
      reindex (reindex (v.interpreted smoothAction)
        (SplitSheaf.p (SplitSheaf.ofDisplay A.cover))) r.splitTotal := by
    simp only [reindex_comp]
    exact congrArg (reindex (v.interpreted smoothAction)) r.splitTotal_cover.symm
  have hf : HEq (((h.interpreted smoothAction).reindex f).reindex
      (SplitSheaf.p (SplitSheaf.ofDisplay B.cover)))
      (((h.interpreted smoothAction).reindex
        (SplitSheaf.p (SplitSheaf.ofDisplay A.cover))).reindex r.splitTotal) := by
    change HEq ((h.interpreted smoothAction).reindex
      (SplitSheaf.p (SplitSheaf.ofDisplay B.cover) ≫ f))
      ((h.interpreted smoothAction).reindex
        (r.splitTotal ≫ SplitSheaf.p (SplitSheaf.ofDisplay A.cover)))
    rw [r.splitTotal_cover]
  have hl := CategoryTheory.heq_comp (hs p) (hs q) (q.restrict_localObject r smoothAction)
    hf (q.restrictLocalComparison_heq r smoothAction)
  have hr := CategoryTheory.heq_comp (hs p) (p.restrict_localObject r smoothAction)
    (q.restrict_localObject r smoothAction) (p.restrictLocalComparison_heq r smoothAction)
    (h.restrict_localArrow_heq r smoothAction)
  have hn := congrArg (fun a => a.reindex r.splitTotal) (h.interpreted_comparison smoothAction)
  exact eq_of_heq (hl.trans ((heq_of_eq hn).trans hr.symm))

/-- The selected global atlas comparison is natural in complete external
families, including their endpoint maps and overlap certificates. -/
theorem restrictComparison_naturality :
    ((h.interpreted smoothAction).reindex f).comp (q.restrictComparison r smoothAction) =
    (p.restrictComparison r smoothAction).comp ((h.restrict r).interpreted smoothAction) := by
  apply Descent.restriction_injective (A := SplitSheaf.ofDisplay B.cover)
  apply (cancel_mono (C := Object (representation smoothAction).action
    (SplitSheaf.extension (SplitSheaf.ofDisplay B.cover)))
    ((q.restrict r).cech smoothAction).toDescent.comparison).mp
  change ((((h.interpreted smoothAction).reindex f).comp
    (q.restrictComparison r smoothAction)).reindex
      (SplitSheaf.p (SplitSheaf.ofDisplay B.cover))).comp
      ((q.restrict r).cech smoothAction).toDescent.comparison =
    (((p.restrictComparison r smoothAction).comp ((h.restrict r).interpreted smoothAction)).reindex
      (SplitSheaf.p (SplitSheaf.ofDisplay B.cover))).comp
      ((q.restrict r).cech smoothAction).toDescent.comparison
  have pullComp {V W : Sheaf topology Type}
      {P Q R : Object (representation smoothAction).action V}
      (a : Arrow P Q) (b : Arrow Q R) (k : W ⟶ V) :
      (a.comp b).reindex k = (a.reindex k).comp (b.reindex k) := by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    rfl
  have assoc {V : Sheaf topology Type}
      {P Q R S : Object (representation smoothAction).action V}
      (a : Arrow P Q) (b : Arrow Q R) (c : Arrow R S) :
      (a.comp b).comp c = a.comp (b.comp c) := Category.assoc (obj := Object (representation smoothAction).action V) a b c
  rw [pullComp, pullComp, assoc, assoc,
    q.restrictComparison_recover, (h.restrict r).interpreted_comparison,
    ← assoc, p.restrictComparison_recover]
  exact h.restrictLocalComparison_naturality r smoothAction

end SquareKit.SmoothCech.Hom
namespace SquareKit.SmoothRepresentedCover.AtlasMap
open CategoryTheory SmoothOpenSite
variable {X Y Z : Sheaf topology Type} {I J K : Type}
  {A : Atlas X I} {B : Atlas Y J} {C : Atlas Z K}

@[simp] theorem ident_splitTotal : (ident A).splitTotal = 𝟙 _ := by
  simp only [splitTotal, ident_total, Category.id_comp, Iso.hom_inv_id]

@[simp] theorem comp_splitTotal {f : Y ⟶ X} {g : Z ⟶ Y}
    (r : AtlasMap A B f) (s : AtlasMap B C g) :
    (r.comp s).splitTotal = s.splitTotal ≫ r.splitTotal := by
  simp only [splitTotal, comp_total, Category.assoc, Iso.inv_hom_id_assoc]

end SquareKit.SmoothRepresentedCover.AtlasMap

namespace SquareKit.SmoothCech.Datum
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothRepresentedCover
open SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X Y Z : Sheaf topology Type} {I J K : Type}
  {A : Atlas X I} {B : Atlas Y J} {C : Atlas Z K}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (p : Datum (d := d) (G := G) (M := M) A)
  {f : Y ⟶ X} (r : AtlasMap A B f)
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

/-- The selected local recovery equation determines the global comparison. -/
theorem restrictComparison_unique
    (h : Arrow (reindex (p.interpreted smoothAction) f)
      ((p.restrict r).interpreted smoothAction))
    (he : (h.reindex (SplitSheaf.p (SplitSheaf.ofDisplay B.cover))).comp
      ((p.restrict r).cech smoothAction).toDescent.comparison =
        p.restrictLocalComparison r smoothAction) :
    h = p.restrictComparison r smoothAction := by
  apply Descent.restriction_injective (A := SplitSheaf.ofDisplay B.cover)
  apply (cancel_mono (C := Object (representation smoothAction).action
    (SplitSheaf.extension (SplitSheaf.ofDisplay B.cover)))
    ((p.restrict r).cech smoothAction).toDescent.comparison).mp
  exact he.trans (p.restrictComparison_recover r smoothAction).symm

/-- Identity refinement gives the equality arrow supplied by the proved
identity law on the complete external datum. -/
theorem restrictComparison_ident : p.restrictComparison (AtlasMap.ident A) smoothAction =
    eqToHom (congrArg (fun q => q.interpreted smoothAction) p.restrict_ident.symm) := by
  symm
  apply p.restrictComparison_unique (AtlasMap.ident A) smoothAction
  have reindexEq {V W : Sheaf topology Type}
      {P Q : Object (representation smoothAction).action V} (h : P = Q) (k : W ⟶ V) :
      (eqToHom h).reindex k = eqToHom (congrArg (fun z => reindex z k) h) := by
    cases h
    rfl
  rw [reindexEq]
  have hc {a b : Descent.Datum (a := (representation smoothAction).action)
      (SplitSheaf.ofDisplay A.cover)} (h : a = b) : HEq a.comparison b.comparison := by
    cases h
    rfl
  have hd : ((p.restrict (AtlasMap.ident A)).cech smoothAction).toDescent =
      (p.cech smoothAction).toDescent :=
    congrArg (fun q => (q.cech smoothAction).toDescent) p.restrict_ident
  have he : HEq (p.restrictLocalComparison (AtlasMap.ident A) smoothAction)
      (p.cech smoothAction).toDescent.comparison := by
    have h := p.restrictLocalComparison_heq (AtlasMap.ident A) smoothAction
    rw [AtlasMap.ident_splitTotal] at h
    exact h
  exact eq_of_heq ((eqToHom_comp_heq (C := Object (representation smoothAction).action
    (SplitSheaf.extension (SplitSheaf.ofDisplay A.cover))) _ _).trans ((hc hd).trans he.symm))

end SquareKit.SmoothCech.Datum
namespace SquareKit.SmoothCech.Datum
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothRepresentedCover
open SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X Y Z : Sheaf topology Type} {I J K : Type}
  {A : Atlas X I} {B : Atlas Y J} {C : Atlas Z K}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (p : Datum (d := d) (G := G) (M := M) A)
  {f : Y ⟶ X} {g : Z ⟶ Y} (r : AtlasMap A B f) (s : AtlasMap B C g)
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

/-- Composition retains the selected comparison and the proved equality of
complete restricted data. -/
theorem restrictComparison_comp :
    (((p.restrictComparison r smoothAction).reindex g).comp
      ((p.restrict r).restrictComparison s smoothAction)).comp
        (eqToHom (congrArg (fun q => q.interpreted smoothAction) (p.restrict_comp r s))) =
      p.restrictComparison (r.comp s) smoothAction := by
  apply p.restrictComparison_unique (r.comp s) smoothAction
  let a := (representation smoothAction).action
  have assoc {V W T : Sheaf topology Type} {P Q : Object a V}
      (h : Arrow P Q) (k : W ⟶ V) (l : T ⟶ W) :
      HEq ((h.reindex k).reindex l) (h.reindex (l ≫ k)) := by rfl
  have pull {V W : Sheaf topology Type} {P Q P' Q' : Object a V}
      (hp : P = P') (hq : Q = Q') (h : Arrow P Q) (h' : Arrow P' Q')
      (hh : HEq h h') (k : W ⟶ V) : HEq (h.reindex k) (h'.reindex k) := by
    cases hp; cases hq; cases hh; rfl
  have changeMap {V W : Sheaf topology Type} {P Q : Object a V}
      (h : Arrow P Q) (k l : W ⟶ V) (he : k = l) :
      HEq (h.reindex k) (h.reindex l) := by cases he; rfl
  have pullComp {V W : Sheaf topology Type} {P Q R : Object a V}
      (h : Arrow P Q) (k : Arrow Q R) (l : W ⟶ V) :
      (h.comp k).reindex l = (h.reindex l).comp (k.reindex l) := by
    apply SheafActionQuotient.Arrow.ext; apply SheafTorsor.Arrow.ext; rfl
  have compAssoc {V : Sheaf topology Type} {P Q R S : Object a V}
      (h : Arrow P Q) (k : Arrow Q R) (l : Arrow R S) :
      (h.comp k).comp l = h.comp (k.comp l) := Category.assoc (obj := Object a V) h k l
  have comparisonHEq {u v : Descent.Datum (a := a) (SplitSheaf.ofDisplay C.cover)}
      (he : u = v) : HEq u.comparison v.comparison := by cases he; rfl
  let q := p.restrict r
  let t := q.restrict s
  let u := p.restrict (r.comp s)
  let pb := SplitSheaf.p (SplitSheaf.ofDisplay B.cover)
  let pc := SplitSheaf.p (SplitSheaf.ofDisplay C.cover)
  let R := p.restrictComparison r smoothAction
  let S := q.restrictComparison s smoothAction
  let L := (R.reindex g).comp S
  have htu : t = u := p.restrict_comp r s
  have hObj : t.interpreted smoothAction = u.interpreted smoothAction :=
    congrArg (fun v => v.interpreted smoothAction) htu
  have hLocal : (t.cech smoothAction).localObject = (u.cech smoothAction).localObject :=
    congrArg (fun v => (v.cech smoothAction).localObject) htu
  have hCast : HEq ((L.comp (eqToHom hObj)).reindex pc) (L.reindex pc) :=
    pull rfl hObj.symm _ _ (comp_eqToHom_heq (C := Object a Z) _ _) pc
  have hCmp : HEq (u.cech smoothAction).toDescent.comparison
      (t.cech smoothAction).toDescent.comparison :=
    comparisonHEq (congrArg (fun v => (v.cech smoothAction).toDescent) htu.symm)
  have hStart := CategoryTheory.heq_comp rfl
    (congrArg (fun v => reindex v pc) hObj.symm) hLocal.symm hCast hCmp
  have hL : (L.reindex pc).comp (t.cech smoothAction).toDescent.comparison =
      ((R.reindex g).reindex pc).comp (q.restrictLocalComparison s smoothAction) := by
    rw [show L = (R.reindex g).comp S from rfl, pullComp, compAssoc]
    rw [show S = q.restrictComparison s smoothAction from rfl,
      q.restrictComparison_recover]
  have hR : HEq ((R.reindex g).reindex pc) ((R.reindex pb).reindex s.splitTotal) :=
    (assoc R g pc).trans ((changeMap R _ _ s.splitTotal_cover.symm).trans
      (assoc R pb s.splitTotal).symm)
  have hSrc : reindex (reindex (reindex (p.interpreted smoothAction) f) g) pc =
      reindex (reindex (reindex (p.interpreted smoothAction) f) pb) s.splitTotal := by
    simp only [reindex_comp]
    exact congrArg (reindex (p.interpreted smoothAction))
      (congrArg (fun k => k ≫ f) s.splitTotal_cover.symm)
  have hMid : reindex (reindex (q.interpreted smoothAction) g) pc =
      reindex (reindex (q.interpreted smoothAction) pb) s.splitTotal := by
    simp only [reindex_comp]
    exact congrArg (reindex (q.interpreted smoothAction)) s.splitTotal_cover.symm
  have hPasting := CategoryTheory.heq_comp hSrc hMid (q.restrict_localObject s smoothAction)
    hR (q.restrictLocalComparison_heq s smoothAction)
  have hRecover := congrArg (fun h => h.reindex s.splitTotal)
    (p.restrictComparison_recover r smoothAction)
  rw [pullComp] at hRecover
  have hErSrc : reindex (reindex (p.interpreted smoothAction) f) pb =
      reindex (reindex (p.interpreted smoothAction)
        (SplitSheaf.p (SplitSheaf.ofDisplay A.cover))) r.splitTotal := by
    simp only [reindex_comp]
    exact congrArg (reindex (p.interpreted smoothAction)) r.splitTotal_cover.symm
  have hEr := pull hErSrc (p.restrict_localObject r smoothAction) _ _
    (p.restrictLocalComparison_heq r smoothAction) s.splitTotal
  have hCompose := (assoc (p.cech smoothAction).toDescent.comparison
    r.splitTotal s.splitTotal).trans
      (changeMap (p.cech smoothAction).toDescent.comparison _ _
        (AtlasMap.comp_splitTotal r s).symm)
  exact eq_of_heq (hStart.trans ((heq_of_eq hL).trans (hPasting.trans
    ((heq_of_eq hRecover).trans (hEr.trans (hCompose.trans
      (p.restrictLocalComparison_heq (r.comp s) smoothAction).symm))))))

end SquareKit.SmoothCech.Datum
namespace SquareKit.SmoothCech.Datum
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothRepresentedCover
open SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X Y : Sheaf topology Type} {I J : Type} {A : Atlas X I} {B : Atlas Y J}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (p : Datum (d := d) (G := G) (M := M) A)
  {f : Y ⟶ X} (r s t : AtlasMap A B f)
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

/-- Two actual atlas maps to a common refinement compare through the same
restricted global object. Composed atlas maps are allowed, with no equality
between their chart choices or their selected descents. -/
def commonComparison : Arrow ((p.restrict r).interpreted smoothAction)
    ((p.restrict s).interpreted smoothAction) :=
  (p.restrictComparison r smoothAction).inverse.comp (p.restrictComparison s smoothAction)

@[simp] theorem commonComparison_ident : p.commonComparison r r smoothAction = Arrow.ident _ := by
  exact (p.restrictComparison r smoothAction).toIso.inv_hom_id

theorem commonComparison_comp :
    (p.commonComparison r s smoothAction).comp (p.commonComparison s t smoothAction) =
      p.commonComparison r t smoothAction := by
  have aux {P Q R S : Object (representation smoothAction).action Y}
      (h : P ⟶ Q) (k : P ⟶ R) (l : P ⟶ S) :
      (Groupoid.inv h ≫ k) ≫ (Groupoid.inv k ≫ l) = Groupoid.inv h ≫ l := by
    simp only [Category.assoc, ← Category.assoc k, Groupoid.comp_inv, Category.id_comp]
  exact aux (p.restrictComparison r smoothAction) (p.restrictComparison s smoothAction)
    (p.restrictComparison t smoothAction)

end SquareKit.SmoothCech.Datum

namespace SquareKit.SmoothCech.Hom
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothRepresentedCover
open SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X Y : Sheaf topology Type} {I J : Type} {A : Atlas X I} {B : Atlas Y J}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable {p q : Datum (d := d) (G := G) (M := M) A}
  (h : Hom p q) {f : Y ⟶ X} (r s : AtlasMap A B f)
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

/-- Common-refinement comparison is natural in complete external arrow families. -/
theorem commonComparison_naturality :
    ((h.restrict r).interpreted smoothAction).comp (q.commonComparison r s smoothAction) =
      (p.commonComparison r s smoothAction).comp ((h.restrict s).interpreted smoothAction) := by
  have aux {P Q P₁ Q₁ P₂ Q₂ : Object (representation smoothAction).action Y}
      (h : P ⟶ Q) (r : P ⟶ P₁) (r' : Q ⟶ Q₁) (s : P ⟶ P₂) (s' : Q ⟶ Q₂)
      (hr : P₁ ⟶ Q₁) (hs : P₂ ⟶ Q₂)
      (nr : h ≫ r' = r ≫ hr) (ns : h ≫ s' = s ≫ hs) :
      hr ≫ (Groupoid.inv r' ≫ s') = (Groupoid.inv r ≫ s) ≫ hs := by
    apply (cancel_epi r).mp
    calc
      r ≫ hr ≫ Groupoid.inv r' ≫ s' = (r ≫ hr) ≫ Groupoid.inv r' ≫ s' := by
        simp only [Category.assoc]
      _ = (h ≫ r') ≫ Groupoid.inv r' ≫ s' := by rw [← nr]
      _ = h ≫ s' := by
        simp only [Category.assoc, ← Category.assoc r', Groupoid.comp_inv, Category.id_comp]
      _ = s ≫ hs := ns
      _ = r ≫ (Groupoid.inv r ≫ s) ≫ hs := by
        simp only [← Category.assoc, Groupoid.comp_inv, Category.id_comp]
  exact aux ((h.interpreted smoothAction).reindex f)
    (p.restrictComparison r smoothAction) (q.restrictComparison r smoothAction)
    (p.restrictComparison s smoothAction) (q.restrictComparison s smoothAction)
    ((h.restrict r).interpreted smoothAction) ((h.restrict s).interpreted smoothAction)
    (h.restrictComparison_naturality r smoothAction) (h.restrictComparison_naturality s smoothAction)

end SquareKit.SmoothCech.Hom

end SelectedRefinement
