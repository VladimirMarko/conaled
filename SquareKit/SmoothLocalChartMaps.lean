import SquareKit.SmoothChartMaps

/-! Experimental local chart maps. Principal covers allow a source chart to
meet arbitrarily many target charts; descent constructs its sheaf map. -/
noncomputable section
open CategoryTheory SquareKit.SmoothAlgebra
namespace SquareKit.EuclideanOpen.Charts
variable {M N : Type} (A : Charts M) (B : Charts N)

/-- Ordinary coordinate descriptions on a cover of each source chart. -/
structure LocalMap (f : M → N) where
  Cover : A.Index → Type
  defining : ∀ i, Cover i → Free (A.domain i).dimension
  covers : ∀ i, Covers (A.domain i) (defining i)
  index : ∀ i, Cover i → B.Index
  coordinate : ∀ i k, subdomain (A.domain i) (defining i k) ⟶ B.domain (index i k)
  agreement : ∀ i k x,
    f (A.coordinate i ((show EuclideanOpen.Map _ _ from subInclusion _ _) x)) =
      B.coordinate (index i k) ((show EuclideanOpen.Map _ _ from coordinate i k) x)

namespace LocalMap
variable {A B} {f : M → N} (l : LocalMap A B f)

def localSection (i : A.Index) (k : l.Cover i) :
    embedding.obj (subdomain (A.domain i) (l.defining i k)) ⟶ B.realization :=
  embedding.map (l.coordinate i k) ≫ B.chart (l.index i k)

theorem local_compatible (i : A.Index) (k k' : l.Cover i) :
    embedding.map (overlapLeft (A.domain i) (l.defining i k) (l.defining i k')) ≫ l.localSection i k =
    embedding.map (overlapRight (A.domain i) (l.defining i k) (l.defining i k')) ≫ l.localSection i k' := by
  let r : B.Relation :=
    ⟨l.index i k,l.index i k',overlap (A.domain i) (l.defining i k) (l.defining i k'),
      overlapLeft _ _ _ ≫ l.coordinate i k,overlapRight _ _ _ ≫ l.coordinate i k',fun x => by
        change B.coordinate _ ((show EuclideanOpen.Map _ _ from l.coordinate i k) _) =
          B.coordinate _ ((show EuclideanOpen.Map _ _ from l.coordinate i k') _)
        rw [← l.agreement,← l.agreement]
        rfl⟩
  simpa only [localSection,← Category.assoc,← Functor.map_comp] using B.chart_compatible r

def sectionMap (i : A.Index) : embedding.obj (A.domain i) ⟶ B.realization :=
  (sheaf_exists_unique (A.domain i) (l.defining i) (l.covers i) B.realization
    (l.localSection i) (l.local_compatible i)).choose

@[reassoc] theorem section_restrict (i : A.Index) (k : l.Cover i) :
    embedding.map (subInclusion (A.domain i) (l.defining i k)) ≫ l.sectionMap i = l.localSection i k :=
  (sheaf_exists_unique (A.domain i) (l.defining i) (l.covers i) B.realization
    (l.localSection i) (l.local_compatible i)).choose_spec.1 k

/-- All ordinary overlap tests agree with the descended section. -/
theorem section_test (i : A.Index) (j : B.Index) (D : Domain)
    (a : D ⟶ A.domain i) (b : D ⟶ B.domain j)
    (h : ∀ x, f (A.coordinate i ((show EuclideanOpen.Map _ _ from a) x)) =
      B.coordinate j ((show EuclideanOpen.Map _ _ from b) x)) :
    embedding.map a ≫ l.sectionMap i = embedding.map b ≫ B.chart j := by
  apply cover_jointly_epic D (fun k => inverseDefining a (l.defining i k))
    (inverse_covers a (l.defining i) (l.covers i)) B.realization
  intro k
  let inc := subInclusion D (inverseDefining a (l.defining i k))
  let t := inverseRestriction a (l.defining i k)
  have square : inc ≫ a = t ≫ subInclusion (A.domain i) (l.defining i k) :=
    (inverseRestriction_square a (l.defining i k)).symm
  let r : B.Relation :=
    ⟨l.index i k,j,subdomain D (inverseDefining a (l.defining i k)),
      t ≫ l.coordinate i k,inc ≫ b,fun x => by
        change B.coordinate _ ((show EuclideanOpen.Map _ _ from l.coordinate i k) _) = _
        rw [← l.agreement]
        exact h ((show EuclideanOpen.Map _ _ from inc) x)⟩
  change embedding.map inc ≫ _ = embedding.map inc ≫ _
  rw [← Category.assoc,← Functor.map_comp,square,Functor.map_comp,Category.assoc,l.section_restrict]
  simpa only [localSection,← Category.assoc,← Functor.map_comp] using B.chart_compatible r

theorem section_compatible : A.Compatible l.sectionMap := by
  intro r
  apply cover_jointly_epic r.domain (fun k => inverseDefining r.left (l.defining r.first k))
    (inverse_covers r.left (l.defining r.first) (l.covers r.first)) B.realization
  intro k
  let D := subdomain r.domain (inverseDefining r.left (l.defining r.first k))
  let inc : D ⟶ r.domain := subInclusion _ _
  let t := inverseRestriction r.left (l.defining r.first k)
  have left : ∀ x, f (A.coordinate r.first ((show EuclideanOpen.Map _ _ from inc ≫ r.left) x)) =
      B.coordinate (l.index r.first k) ((show EuclideanOpen.Map _ _ from t ≫ l.coordinate r.first k) x) :=
    fun x => l.agreement r.first k ((show EuclideanOpen.Map _ _ from t) x)
  have right : ∀ x, f (A.coordinate r.second ((show EuclideanOpen.Map _ _ from inc ≫ r.right) x)) =
      B.coordinate (l.index r.first k) ((show EuclideanOpen.Map _ _ from t ≫ l.coordinate r.first k) x) := by
    intro x
    exact (congrArg f (r.agreement ((show EuclideanOpen.Map _ _ from inc) x))).symm.trans (left x)
  change embedding.map inc ≫ _ = embedding.map inc ≫ _
  simpa only [Functor.map_comp,Category.assoc] using
    (l.section_test r.first _ D (inc ≫ r.left) (t ≫ l.coordinate r.first k) left).trans
      (l.section_test r.second _ D (inc ≫ r.right) (t ≫ l.coordinate r.first k) right).symm

def realize : A.realization ⟶ B.realization := A.descend l.sectionMap l.section_compatible

@[reassoc (attr := simp)] theorem chart_realize (i : A.Index) :
    A.chart i ≫ l.realize = l.sectionMap i := A.chart_descend _ _ i

@[reassoc] theorem test (i : A.Index) (j : B.Index) (D : Domain)
    (a : D ⟶ A.domain i) (b : D ⟶ B.domain j)
    (h : ∀ x, f (A.coordinate i ((show EuclideanOpen.Map _ _ from a) x)) =
      B.coordinate j ((show EuclideanOpen.Map _ _ from b) x)) :
    embedding.map a ≫ A.chart i ≫ l.realize = embedding.map b ≫ B.chart j := by
  rw [chart_realize]
  exact l.section_test i j D a b h

/-- Independence of every cover and chart choice for the same ordinary map. -/
theorem realize_eq (l' : LocalMap A B f) : l.realize = l'.realize := by
  apply A.hom_ext
  intro i
  rw [chart_realize,chart_realize]
  apply cover_jointly_epic (A.domain i) (l.defining i) (l.covers i) B.realization
  intro k
  rw [section_restrict]
  exact (l'.section_test i (l.index i k) _ (subInclusion _ _) (l.coordinate i k)
    (l.agreement i k)).symm

end LocalMap
end SquareKit.EuclideanOpen.Charts
