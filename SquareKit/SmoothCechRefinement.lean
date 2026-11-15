import SquareKit.SmoothCechGauge

/-! Represented chart maps over a base map, with derived intersection maps. -/
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
  simpa only [Category.assoc] using congrArg (fun h => h ≫ f) (B.tripleSquare i j k).w

def triple (i j k : J) : B.triple i j k ⟶ A.triple (r.index i) (r.index j) (r.index k) :=
  (homEquiv _ _).symm ((A.tripleSquare (r.index i) (r.index j) (r.index k)).lift
    (embedding.map (B.firstSecond i j k ≫ r.pair i j))
    (embedding.map (B.third i j k ≫ r.chart k)) (r.triple_w i j k))

theorem triple_map (i j k : J) : embedding.map (r.triple i j k) =
    (A.tripleSquare (r.index i) (r.index j) (r.index k)).lift
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
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (Model d) ∞ M]

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

theorem restrict_ident (p : Datum (d := d) (G := G) (M := M) A) :
    (Hom.ident p).restrict r = Hom.ident (p.restrict r) := by
  apply Hom.ext
  funext j
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  rfl

theorem restrict_comp {s : Datum (d := d) (G := G) (M := M) A}
    (h : Hom p q) (k : Hom q s) : (h.comp k).restrict r = (h.restrict r).comp (k.restrict r) := by
  apply Hom.ext
  funext j
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  rfl

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
