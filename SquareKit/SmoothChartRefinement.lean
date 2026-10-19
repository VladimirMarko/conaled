import SquareKit.SmoothChartMaps

/-! Experimental descent along ordinary chart refinements. Cover data and
lifts are ordinary smooth maps; the inverse sheaf map is constructed by descent. -/
noncomputable section
open CategoryTheory SquareKit.SmoothAlgebra
namespace SquareKit.EuclideanOpen.Charts
variable {M : Type} {A B : Charts M}

/-- A chartwise identity map with principal covers admitting lifts to the
refining charts. This is ordinary geometric data, not a sheaf descent premise. -/
structure Refinement (B A : Charts M) where
  map : Map B A
  point_identity : map.point = id
  Cover : A.Index → Type
  defining : ∀ i, Cover i → Free (A.domain i).dimension
  covers : ∀ i, Covers (A.domain i) (defining i)
  index : ∀ i, Cover i → B.Index
  lift : ∀ i k, subdomain (A.domain i) (defining i k) ⟶ B.domain (index i k)
  agreement : ∀ i k x,
    A.coordinate i ((show EuclideanOpen.Map _ _ from subInclusion (A.domain i) (defining i k)) x) =
    B.coordinate (index i k) ((show EuclideanOpen.Map _ _ from lift i k) x)

namespace Refinement
variable (r : Refinement B A)

def localSection (i : A.Index) (k : r.Cover i) :
    embedding.obj (subdomain (A.domain i) (r.defining i k)) ⟶ B.realization :=
  embedding.map (r.lift i k) ≫ B.chart (r.index i k)

theorem local_compatible (i : A.Index) (k l : r.Cover i) :
    embedding.map (overlapLeft (A.domain i) (r.defining i k) (r.defining i l)) ≫ r.localSection i k =
    embedding.map (overlapRight (A.domain i) (r.defining i k) (r.defining i l)) ≫ r.localSection i l := by
  let rel : B.Relation :=
    ⟨r.index i k, r.index i l, overlap (A.domain i) (r.defining i k) (r.defining i l),
      overlapLeft _ _ _ ≫ r.lift i k, overlapRight _ _ _ ≫ r.lift i l, fun x => by
        change B.coordinate _ ((show EuclideanOpen.Map _ _ from r.lift i k) _) =
          B.coordinate _ ((show EuclideanOpen.Map _ _ from r.lift i l) _)
        rw [← r.agreement, ← r.agreement]
        rfl⟩
  simpa only [localSection, ← Category.assoc, ← Functor.map_comp] using B.chart_compatible rel

def sectionMap (i : A.Index) : embedding.obj (A.domain i) ⟶ B.realization :=
  (sheaf_exists_unique (A.domain i) (r.defining i) (r.covers i) B.realization
    (r.localSection i) (r.local_compatible i)).choose

@[reassoc] theorem section_restrict (i : A.Index) (k : r.Cover i) :
    embedding.map (subInclusion (A.domain i) (r.defining i k)) ≫ r.sectionMap i =
      r.localSection i k :=
  (sheaf_exists_unique (A.domain i) (r.defining i) (r.covers i) B.realization
    (r.localSection i) (r.local_compatible i)).choose_spec.1 k

/-- A descended chart section agrees with any refining chart on every ordinary
smooth test on their overlap. Inverse-image covers make this a local assertion. -/
theorem section_test (i : A.Index) (j : B.Index) (D : Domain)
    (a : D ⟶ A.domain i) (b : D ⟶ B.domain j)
    (h : ∀ x, A.coordinate i ((show EuclideanOpen.Map _ _ from a) x) =
      B.coordinate j ((show EuclideanOpen.Map _ _ from b) x)) :
    embedding.map a ≫ r.sectionMap i = embedding.map b ≫ B.chart j := by
  apply cover_jointly_epic D (fun k => inverseDefining a (r.defining i k))
    (inverse_covers a (r.defining i) (r.covers i)) B.realization
  intro k
  let inc := subInclusion D (inverseDefining a (r.defining i k))
  let t := inverseRestriction a (r.defining i k)
  have square : inc ≫ a = t ≫ subInclusion (A.domain i) (r.defining i k) :=
    (inverseRestriction_square a (r.defining i k)).symm
  let rel : B.Relation :=
    ⟨r.index i k, j, subdomain D (inverseDefining a (r.defining i k)),
      t ≫ r.lift i k, inc ≫ b, fun x => by
        change B.coordinate _ ((show EuclideanOpen.Map _ _ from r.lift i k) _) = _
        rw [← r.agreement]
        exact h ((show EuclideanOpen.Map _ _ from inc) x)⟩
  change embedding.map inc ≫ _ = embedding.map inc ≫ _
  rw [← Category.assoc, ← Functor.map_comp, square, Functor.map_comp, Category.assoc,
    r.section_restrict]
  simpa only [localSection, ← Category.assoc, ← Functor.map_comp] using B.chart_compatible rel

theorem section_compatible : A.Compatible r.sectionMap := by
  intro s
  apply cover_jointly_epic s.domain (fun k => inverseDefining s.left (r.defining s.first k))
    (inverse_covers s.left (r.defining s.first) (r.covers s.first)) B.realization
  intro k
  let D := subdomain s.domain (inverseDefining s.left (r.defining s.first k))
  let inc : D ⟶ s.domain := subInclusion _ _
  let t := inverseRestriction s.left (r.defining s.first k)
  have left : ∀ x, A.coordinate s.first ((show EuclideanOpen.Map _ _ from inc ≫ s.left) x) =
      B.coordinate (r.index s.first k) ((show EuclideanOpen.Map _ _ from t ≫ r.lift s.first k) x) :=
    fun x => r.agreement s.first k ((show EuclideanOpen.Map _ _ from t) x)
  have right : ∀ x, A.coordinate s.second ((show EuclideanOpen.Map _ _ from inc ≫ s.right) x) =
      B.coordinate (r.index s.first k) ((show EuclideanOpen.Map _ _ from t ≫ r.lift s.first k) x) := by
    intro x
    exact (s.agreement ((show EuclideanOpen.Map _ _ from inc) x)).symm.trans (left x)
  change embedding.map inc ≫ _ = embedding.map inc ≫ _
  simpa only [Functor.map_comp, Category.assoc] using
    (r.section_test s.first _ D (inc ≫ s.left) (t ≫ r.lift s.first k) left).trans
      (r.section_test s.second _ D (inc ≫ s.right) (t ≫ r.lift s.first k) right).symm

def inverse : A.realization ⟶ B.realization := A.descend r.sectionMap r.section_compatible

@[reassoc (attr := simp)] theorem chart_inverse (i : A.Index) :
    A.chart i ≫ r.inverse = r.sectionMap i := A.chart_descend _ _ i

theorem map_inverse : r.map.realize ≫ r.inverse = 𝟙 B.realization := by
  apply B.hom_ext
  intro j
  rw [← Category.assoc, Map.chart_realize, Category.assoc, chart_inverse, Category.comp_id]
  have h : ∀ x, A.coordinate (r.map.index j) ((show EuclideanOpen.Map _ _ from r.map.coordinate j) x) =
      B.coordinate j x := by
    intro x
    rw [← r.map.agreement, r.point_identity]
    rfl
  have he := r.section_test (r.map.index j) j (B.domain j) (r.map.coordinate j) (𝟙 _) h
  rw [embedding.map_id, Category.id_comp] at he
  exact he

theorem inverse_map : r.inverse ≫ r.map.realize = 𝟙 A.realization := by
  apply A.hom_ext
  intro i
  simp only [← Category.assoc, chart_inverse, Category.comp_id]
  apply cover_jointly_epic (A.domain i) (r.defining i) (r.covers i) A.realization
  intro k
  rw [← Category.assoc, section_restrict]
  change (embedding.map (r.lift i k) ≫ B.chart (r.index i k)) ≫ r.map.realize = _
  rw [Category.assoc, Map.chart_realize, ← Category.assoc, ← Functor.map_comp]
  apply A.chart_compatible
    (⟨r.map.index (r.index i k), i, subdomain (A.domain i) (r.defining i k),
      r.lift i k ≫ r.map.coordinate (r.index i k), subInclusion _ _, ?_⟩ : A.Relation)
  intro x
  change A.coordinate _ ((show EuclideanOpen.Map _ _ from r.map.coordinate _) _) = _
  rw [← r.map.agreement, r.point_identity]
  exact (r.agreement i k x).symm

/-- An actual refinement isomorphism with the chartwise forward map. -/
def iso : B.realization ≅ A.realization :=
  ⟨r.map.realize, r.inverse, r.map_inverse, r.inverse_map⟩

end Refinement
end SquareKit.EuclideanOpen.Charts
