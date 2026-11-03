import SquareKit.SmoothLocalChartMaps

/-! Experimental laws for arbitrary locally chartwise maps, proved by descent. -/
noncomputable section
open CategoryTheory SquareKit.SmoothAlgebra
namespace SquareKit.EuclideanOpen.Charts.LocalMap
variable {M N P : Type} {A : Charts M} {B : Charts N} {C : Charts P}

theorem realize_id (l : LocalMap A A id) : l.realize = 𝟙 A.realization := by
  apply A.hom_ext
  intro i
  rw [chart_realize,Category.comp_id]
  have h := l.section_test i i (A.domain i) (𝟙 _) (𝟙 _) (fun _ => rfl)
  rw [embedding.map_id,Category.id_comp,Category.id_comp] at h
  exact h

/-- Composition is independent of the three separately chosen local covers. -/
theorem realize_comp {f : M → N} {g : N → P}
    (l : LocalMap A B f) (m : LocalMap B C g) (n : LocalMap A C (g ∘ f)) :
    n.realize = l.realize ≫ m.realize := by
  apply A.hom_ext
  intro i
  rw [chart_realize,← Category.assoc,chart_realize]
  apply cover_jointly_epic (A.domain i) (l.defining i) (l.covers i) C.realization
  intro k
  rw [← Category.assoc,l.section_restrict]
  let D := subdomain (A.domain i) (l.defining i k)
  let a := l.coordinate i k
  apply cover_jointly_epic D (fun j => inverseDefining a (m.defining (l.index i k) j))
    (inverse_covers a (m.defining (l.index i k)) (m.covers (l.index i k))) C.realization
  intro j
  let E := subdomain D (inverseDefining a (m.defining (l.index i k) j))
  let inc : E ⟶ D := subInclusion _ _
  let t := inverseRestriction a (m.defining (l.index i k) j)
  let b := t ≫ m.coordinate (l.index i k) j
  have hb : ∀ x, g (B.coordinate (l.index i k) ((show EuclideanOpen.Map _ _ from inc ≫ a) x)) =
      C.coordinate (m.index (l.index i k) j) ((show EuclideanOpen.Map _ _ from b) x) :=
    fun x => m.agreement (l.index i k) j ((show EuclideanOpen.Map _ _ from t) x)
  have ha : ∀ x, (g ∘ f) (A.coordinate i
      ((show EuclideanOpen.Map _ _ from inc ≫ subInclusion (A.domain i) (l.defining i k)) x)) =
      C.coordinate (m.index (l.index i k) j) ((show EuclideanOpen.Map _ _ from b) x) := by
    intro x
    change g (f (A.coordinate i ((show EuclideanOpen.Map _ _ from subInclusion (A.domain i) (l.defining i k)) ((show EuclideanOpen.Map _ _ from inc) x)))) = _
    rw [l.agreement]
    exact hb x
  have hn := n.section_test i _ E (inc ≫ subInclusion _ _) b ha
  have hm := m.section_test (l.index i k) _ E (inc ≫ a) b hb
  change embedding.map inc ≫ _ = embedding.map inc ≫ _
  simpa only [localSection,Functor.map_comp,Category.assoc,chart_realize] using hn.trans hm.symm

/-- A local description of a previously whole-chart map gives the same arrow. -/
theorem realize_whole (f : Map A B) (l : LocalMap A B f.point) : l.realize = f.realize := by
  apply A.hom_ext
  intro i
  rw [chart_realize,Map.chart_realize]
  have h := l.section_test i (f.index i) (A.domain i) (𝟙 _) (f.coordinate i) (f.agreement i)
  rw [embedding.map_id,Category.id_comp] at h
  exact h

end SquareKit.EuclideanOpen.Charts.LocalMap
