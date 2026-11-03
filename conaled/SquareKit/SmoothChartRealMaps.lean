import SquareKit.SmoothChartRealSections
import SquareKit.SmoothLocalChartMaps

/-! The ordinary point function of an arbitrary arrow between chart realizations. -/
noncomputable section
open CategoryTheory
namespace SquareKit.EuclideanOpen.Charts
open SmoothOpenSite SmoothAlgebra
variable {M N : Type} (A : Charts M) (B : Charts N)
    (ha : ∀ x, ∃ i y, A.coordinate i y = x)
    (hb : ∀ x, ∃ i y, B.coordinate i y = x)

def realMap (h : A.realization ⟶ B.realization) (x : M) : N :=
  B.realEquiv hb (realSections.map h ((A.realEquiv ha).symm x))

theorem realMap_chart (h : A.realization ⟶ B.realization)
    (i : A.Index) (x : Points (A.domain i)) :
    A.realMap B ha hb h (A.coordinate i x) =
      B.realEquiv hb (realSections.map h
        (realSections.map (A.chart i) ((realSectionEquiv _).symm x))) := by
  have he := A.realEquiv_chart ha i ((realSectionEquiv _).symm x)
  rw [Equiv.apply_symm_apply] at he
  exact congrArg (fun z => B.realEquiv hb (realSections.map h z))
    ((A.realEquiv ha).symm_apply_eq.mpr he.symm)

theorem realMap_factor (h : A.realization ⟶ B.realization)
    (i : A.Index) (j : B.Index) (D : Domain) (u : D ⟶ A.domain i) (v : D ⟶ B.domain j)
    (hv : embedding.map u ≫ A.chart i ≫ h = embedding.map v ≫ B.chart j) (z : Points D) :
    A.realMap B ha hb h (A.coordinate i ((show EuclideanOpen.Map _ _ from u) z)) =
      B.coordinate j ((show EuclideanOpen.Map _ _ from v) z) := by
  let a := (realSectionEquiv D).symm z
  have hi : (realSectionEquiv _).symm ((show EuclideanOpen.Map _ _ from u) z) =
      realSections.map (embedding.map u) a := by
    apply (realSectionEquiv _).injective
    rw [Equiv.apply_symm_apply, realSectionEquiv_naturality]
    exact congrArg (show EuclideanOpen.Map _ _ from u).toFun
      ((realSectionEquiv _).apply_symm_apply z).symm
  rw [realMap_chart, hi]
  have ht := ConcreteCategory.congr_hom (congrArg realSections.map hv) a
  simp only [realSections.map_comp, types_comp_apply] at ht
  rw [ht, B.realEquiv_chart, realSectionEquiv_naturality]
  exact congrArg (fun t => B.coordinate j ((show EuclideanOpen.Map _ _ from v) t))
    ((realSectionEquiv D).apply_symm_apply z)

theorem realMap_local {f : M → N} (l : LocalMap A B f)
    (i : A.Index) (k : l.Cover i)
    (z : Points (subdomain (A.domain i) (l.defining i k))) :
    A.realMap B ha hb l.realize
      (A.coordinate i ((subInclusion _ _).toFun z)) =
      f (A.coordinate i ((subInclusion _ _).toFun z)) :=
  (A.realMap_factor B ha hb l.realize i (l.index i k) _ (subInclusion _ _) (l.coordinate i k)
    (l.test i (l.index i k) _ (subInclusion _ _) (l.coordinate i k) (l.agreement i k)) z).trans
      (l.agreement i k z).symm

/-- Interpretation recovers the supplied ordinary function on every point. -/
theorem realMap_realize {f : M → N} (l : LocalMap A B f) :
    A.realMap B ha hb l.realize = f := by
  funext x
  obtain ⟨i, y, rfl⟩ := ha x
  obtain ⟨k, hk⟩ := l.covers i y
  exact A.realMap_local B ha hb l i k ⟨y.val, mul_ne_zero y.property hk⟩

include ha hb in
theorem realize_injective {f g : M → N} (l : LocalMap A B f) (k : LocalMap A B g)
    (h : l.realize = k.realize) : f = g := by
  rw [← A.realMap_realize B ha hb l, ← A.realMap_realize B ha hb k, h]

end SquareKit.EuclideanOpen.Charts
