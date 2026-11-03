import SquareKit.SmoothLocalChartMaps

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

/-- The identity-function instance of ordinary local chart descent. -/
def localMap : LocalMap A B id :=
  ⟨r.Cover, r.defining, r.covers, r.index, r.lift, r.agreement⟩

abbrev localSection := r.localMap.localSection
abbrev local_compatible := r.localMap.local_compatible
abbrev sectionMap := r.localMap.sectionMap
@[reassoc] theorem section_restrict (i : A.Index) (k : r.Cover i) :
    embedding.map (subInclusion (A.domain i) (r.defining i k)) ≫ r.sectionMap i = r.localSection i k :=
  r.localMap.section_restrict i k
abbrev section_test := r.localMap.section_test
abbrev section_compatible := r.localMap.section_compatible

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
